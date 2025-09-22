import argparse
import ast
import hashlib
import json
import sys
import io
import re
import tokenize
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, List, Optional, Tuple, Union

try:
    from cognitive_complexity.api import get_cognitive_complexity
except Exception:                                                                         
    def get_cognitive_complexity(node: ast.AST) -> int:                
        raise RuntimeError(
            "Falta la dependencia 'cognitive_complexity'. Ejecuta: pip install -r requirements.txt"
        )


RULE_KEY = "python:S3776"


@dataclass
class FunctionInfo:
    file_path: Path
    rel_path: Path
    qualname: str
    lineno: int
    col_offset: int
    name: str
    node: ast.AST


def walk_python_files(root: Path) -> Iterable[Path]:
    exclude_dirs = {
        ".git",
        "__pycache__",
        ".mypy_cache",
        ".pytest_cache",
        "env",
        "venv",
        ".venv",
        "build",
        "dist",
        ".tox",
        ".idea",
        ".vscode",
    }
    for p in root.rglob("*.py"):
        parts = set(p.parts)
        if parts & exclude_dirs:
            continue
        yield p


class FunctionCollector(ast.NodeVisitor):
    def __init__(self, file_path: Path, rel_path: Path) -> None:
        self.file_path = file_path
        self.rel_path = rel_path
        self.stack: List[str] = []
        self.items: List[FunctionInfo] = []

    def visit_ClassDef(self, node: ast.ClassDef) -> None:                          
        self.stack.append(node.name)
        self.generic_visit(node)
        self.stack.pop()

    def _add_function(self, node: ast.AST, name: str, lineno: int, col: int) -> None:
        qual = ".".join(self.stack + [name]) if self.stack else name
        self.items.append(
            FunctionInfo(
                file_path=self.file_path,
                rel_path=self.rel_path,
                qualname=qual,
                lineno=lineno,
                col_offset=col,
                name=name,
                node=node,
            )
        )

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:                          
        self._add_function(node, node.name, node.lineno, node.col_offset)
                                
        self.stack.append(node.name)
        self.generic_visit(node)
        self.stack.pop()

    def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef) -> None:                          
        self._add_function(node, node.name, node.lineno, node.col_offset)
        self.stack.append(node.name)
        self.generic_visit(node)
        self.stack.pop()


def collect_functions(file_path: Path, project_root: Path) -> List[FunctionInfo]:
    try:
        text = file_path.read_text(encoding="utf-8")
    except UnicodeDecodeError:
        text = file_path.read_text(encoding="latin-1", errors="ignore")
    try:
        tree = ast.parse(text, filename=str(file_path))
    except SyntaxError:
        return []
    rel = file_path.relative_to(project_root)
    collector = FunctionCollector(file_path, rel)
    collector.visit(tree)
    return collector.items


def compute_severity(value: int, major: int, critical: int) -> str:
    if value >= critical:
        return "CRITICAL"
    if value >= major:
        return "MAJOR"
    return "MINOR"


def component_key(project_key: str, rel_path: Path) -> str:
    return f"{project_key}:{rel_path.as_posix()}"


def _offset_range_for_keyword(node: ast.AST, keyword_len: int) -> Tuple[int, int]:
                                          
    start = getattr(node, "col_offset", 0) or 0
    end = start + max(1, keyword_len)
    return start, end


class ComplexityTracer:
    def __init__(self, project_key: str, rel_path: Path, func_name: str, source: str) -> None:
        self.project_key = project_key
        self.rel_path = rel_path
        self.func_name = func_name
        self.source = source
        self.lines: List[str] = source.splitlines()
                                                                         
        self.entries: List[Tuple[int, int, int, int, bool]] = []

    def _component(self) -> str:
        return f"{self.project_key}:{self.rel_path.as_posix()}"

    def _add_at(self, lineno: int, start_col: int, end_col: int, inc: int, apply_nesting: bool = True) -> None:
        self.entries.append((lineno, start_col, end_col, inc, apply_nesting))

    def _line(self, lineno: int) -> str:
        if 1 <= lineno <= len(self.lines):
            return self.lines[lineno - 1]
        return ""

                                 
    def _nest(self):
        class Ctx:
            def __init__(self, outer: "ComplexityTracer"):
                self.outer = outer
            def __enter__(self):
                self.outer.nesting += 1
            def __exit__(self, exc_type, exc, tb):
                self.outer.nesting -= 1
        return Ctx(self)

    def _find_else_token(self, node: Union[ast.If, ast.For, ast.While]) -> Optional[Tuple[int, int, int]]:
        if not getattr(node, "orelse", None):
            return None
        if isinstance(node, ast.If) and len(node.orelse) == 1 and isinstance(node.orelse[0], ast.If):
                                                              
            return None
        first = node.orelse[0]
        start_line = getattr(first, "lineno", None)
        if not isinstance(start_line, int):
            return None
        base_indent = getattr(node, "col_offset", 0) or 0
                                                             
        for lno in range(start_line - 1, max(1, start_line - 5) - 1, -1):
            line = self._line(lno)
            idx = line.find("else")
            if idx != -1:
                                                            
                if idx <= base_indent + 2 and (idx + 4 <= len(line)):
                                                 
                    before_ok = (idx == 0) or (not line[idx - 1].isalnum())
                    after_ok = (idx + 4 < len(line) and line[idx + 4] in (":", " "))
                    if before_ok and after_ok:
                        return (lno, idx, idx + 4)
        return None

    def _process_node_itself(self, node: ast.AST, inc_by: int) -> Tuple[int, int, bool]:
                                                                                            
        control = (ast.If, ast.For, ast.While, ast.IfExp, ast.ExceptHandler)
        incrementers = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)
        if isinstance(node, control):
                                          
            if isinstance(node, ast.IfExp):
                inc_by += 1
                return inc_by, max(1, inc_by), True
            elif isinstance(node, ast.If) and node.orelse and len(node.orelse) == 1 and isinstance(node.orelse[0], ast.If):
                      
                return inc_by, max(1, inc_by), True
            elif isinstance(node, ast.ExceptHandler):
                inc_by += 1
                return inc_by, max(1, inc_by), True
            elif isinstance(node, (ast.If, ast.For, ast.While)):
                has_else = bool(getattr(node, "orelse", None)) and not (
                    isinstance(node, ast.If) and len(node.orelse) == 1 and isinstance(node.orelse[0], ast.If)
                )
                inc_by += 1
                base = max(1, inc_by) + (1 if has_else else 0)
                return inc_by, base, True
        elif isinstance(node, incrementers):
            inc_by += 1
            return inc_by, 0, True
        elif isinstance(node, ast.BoolOp):
                                                              
            inner = sum(1 for n in ast.walk(node) if isinstance(n, ast.BoolOp))
            return inc_by, inner, False
        return inc_by, 0, True

    def _trace(self, node: ast.AST, increment_by: int = 0) -> None:
        inc_next, base, should_iter = self._process_node_itself(node, increment_by)

                                                                 
        if base:
            if isinstance(node, ast.If):
                pos = getattr(node, "col_offset", 0) or 0
                line = node.lineno
                                                               
                has_else = bool(node.orelse) and not (len(node.orelse) == 1 and isinstance(node.orelse[0], ast.If))
                                                                                                   
                if_inc = max(1, inc_next)
                self._add_at(line, pos, pos + 2, if_inc, apply_nesting=(if_inc > 1))
                           
                if has_else:
                    et = self._find_else_token(node)
                    if et:
                        eline, ecol, eend = et
                        self._add_at(eline, ecol, eend, 1, apply_nesting=False)
            elif isinstance(node, ast.For):
                pos = getattr(node, "col_offset", 0) or 0
                line = node.lineno
                has_else = bool(getattr(node, "orelse", None))
                for_inc = max(1, inc_next)
                self._add_at(line, pos, pos + 3, for_inc, apply_nesting=(for_inc > 1))
                if has_else:
                    et = self._find_else_token(node)
                    if et:
                        eline, ecol, eend = et
                        self._add_at(eline, ecol, eend, 1, apply_nesting=False)
            elif isinstance(node, ast.AsyncFor):
                                                    
                start = getattr(node, "col_offset", 0) or 0
                line = node.lineno
                m = re.search(r"\bfor\b", self._line(line)[start:])
                s = start + (m.start() if m else 0)
                e = s + 3
                has_else = bool(getattr(node, "orelse", None))
                for_inc = max(1, inc_next)
                self._add_at(line, s, e, for_inc, apply_nesting=(for_inc > 1))
                if has_else:
                    et = self._find_else_token(node)                          
                    if et:
                        eline, ecol, eend = et
                        self._add_at(eline, ecol, eend, 1, apply_nesting=False)
            elif isinstance(node, ast.While):
                pos = getattr(node, "col_offset", 0) or 0
                line = node.lineno
                has_else = bool(getattr(node, "orelse", None))
                while_inc = max(1, inc_next)
                self._add_at(line, pos, pos + 5, while_inc, apply_nesting=(while_inc > 1))
                if has_else:
                    et = self._find_else_token(node)                          
                    if et:
                        eline, ecol, eend = et
                        self._add_at(eline, ecol, eend, 1, apply_nesting=False)
            elif isinstance(node, ast.IfExp):
                seg = ast.get_source_segment(self.source, node) or ""
                base_line = getattr(node, "lineno", 1) or 1
                base_col = getattr(node, "col_offset", 0) or 0
                marked = False
                try:
                    for tok in tokenize.generate_tokens(io.StringIO(seg).readline):
                        if tok.type == tokenize.NAME and tok.string == "if":
                            line_off = tok.start[0]
                            col_off = tok.start[1]
                            abs_line = base_line + (line_off - 1)
                            abs_col = base_col + col_off if line_off == 1 else col_off
                            ifexp_inc = max(1, inc_next)
                            self._add_at(abs_line, abs_col, abs_col + 2, ifexp_inc, apply_nesting=(ifexp_inc > 1))
                            marked = True
                            break
                except Exception:
                    pass
                if not marked:
                    pos = getattr(node, "col_offset", 0) or 0
                    ifexp_inc = max(1, inc_next)
                    self._add_at(node.lineno, pos, pos + 2, ifexp_inc, apply_nesting=(ifexp_inc > 1))
            elif isinstance(node, ast.ExceptHandler):
                pos = getattr(node, "col_offset", 0) or 0
                exc_inc = max(1, inc_next)
                self._add_at(node.lineno, pos, pos + 6, exc_inc, apply_nesting=(exc_inc > 1))
            elif isinstance(node, ast.BoolOp):
                                                                              
                seg = ast.get_source_segment(self.source, node) or ""
                base_line = getattr(node, "lineno", 1) or 1
                base_col = getattr(node, "col_offset", 0) or 0
                try:
                    for tok in tokenize.generate_tokens(io.StringIO(seg).readline):
                        if tok.type == tokenize.NAME and tok.string in ("and", "or"):
                            line_off = tok.start[0]
                            col_off = tok.start[1]
                            abs_line = base_line + (line_off - 1)
                            abs_col = base_col + col_off if line_off == 1 else col_off
                                                                         
                            self._add_at(abs_line, abs_col, abs_col + len(tok.string), base, apply_nesting=False)
                            break
                except Exception:
                    pass
                                                                                              

                                           
        if should_iter:
            for child in ast.iter_child_nodes(node):
                self._trace(child, increment_by=inc_next)

    def run(self, node: ast.AST) -> None:
                                                                                        
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                                                                                   
            try:
                from cognitive_complexity.api import is_decorator                
            except Exception:
                is_decorator = None                
            target_fn = node
            if is_decorator is not None:
                while is_decorator(target_fn):                          
                    inner = target_fn.body[0]
                    if isinstance(inner, (ast.FunctionDef, ast.AsyncFunctionDef)):
                        target_fn = inner
                    else:
                        break
            for child in target_fn.body:
                self._trace(child, increment_by=0)
        else:
            self._trace(node, increment_by=0)
                                                                         
        try:
            from cognitive_complexity.api import has_recursive_calls                
        except Exception:
            has_recursive_calls = None                
        if has_recursive_calls is not None and isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if has_recursive_calls(node):                          
                for n in ast.walk(node):
                    if isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == self.func_name:
                        lineno = getattr(n.func, "lineno", None)
                        col = getattr(n.func, "col_offset", None)
                        if isinstance(lineno, int) and isinstance(col, int):
                            self._add_at(lineno, col, col + len(self.func_name), 1, apply_nesting=False)
                            break

    def to_flows(self) -> List[dict]:
        flows: List[dict] = []
        comp = self._component()
        for lineno, start, end, inc, apply_nesting in self.entries:
            if inc <= 1:
                msg = "+1"
            else:
                                                                                        
                if apply_nesting:
                    nesting = max(0, inc - 1)
                    msg = f"+{inc} (incl {nesting} for nesting)"
                else:
                    msg = f"+{inc}"
            flows.append(
                {
                    "locations": [
                        {
                            "component": comp,
                            "textRange": {
                                "startLine": lineno,
                                "endLine": lineno,
                                "startOffset": start,
                                "endOffset": end,
                            },
                            "msg": msg,
                            "msgFormattings": [],
                        }
                    ]
                }
            )
        return flows


def _last_non_ws_col(line: str) -> int:
    i = len(line)
    while i > 0 and line[i - 1] in (" ", "\t", "\r", "\n"):
        i -= 1
    return i


def _compute_issue_text_range(
    func: FunctionInfo,
    source: str,
    mode: str = "signature",
) -> Tuple[int, int, int, int]:
                                                          
    lines = source.splitlines()
    start_line = func.lineno
    end_line = func.lineno
    start_offset = func.col_offset
    end_offset = start_offset + len(func.name)

    header = lines[start_line - 1] if 1 <= start_line <= len(lines) else ""

                                                  
    idx_def = header.find("def", start_offset)
    if idx_def == -1:
        idx_async = header.find("async", start_offset)
        if idx_async != -1:
            idx_def = header.find("def", idx_async + 5)
    if idx_def != -1:
        idx_name = header.find(func.name, idx_def + 3)
        if idx_name != -1:
            name_start = idx_name
        else:
            name_start = start_offset
    else:
        name_start = start_offset

    if mode == "keyword":
                                                       
        if idx_def != -1:
            start_offset = idx_def
            end_offset = idx_def + 3
        else:
            idx_async = header.find("async", start_offset)
            if idx_async != -1:
                start_offset = idx_async
                end_offset = idx_async + 5
    elif mode == "signature":
                                                     
        start_offset = name_start
        end_offset = start_offset + len(func.name)
    elif mode == "body":
                                                                   
        start_offset = idx_def if idx_def != -1 else start_offset
                                                                      
        node = func.node
        end_line = int(getattr(node, "end_lineno", 0) or 0) or start_line
        end_col = getattr(node, "end_col_offset", None)
        if end_col is None:
            tail = lines[end_line - 1] if 1 <= end_line <= len(lines) else ""
            end_offset = _last_non_ws_col(tail)
        else:
            end_offset = int(end_col)
    else:
                               
        start_offset = name_start
        end_offset = start_offset + len(func.name)

    return start_line, end_line, start_offset, end_offset


def make_issue(
    project_key: str,
    func: FunctionInfo,
    complexity: int,
    file_source: Optional[str] = None,
    issue_range_mode: str = "signature",
) -> dict:
                                                  
    if not file_source:
        file_source = ""
    start_line, end_line, start_offset, end_offset = _compute_issue_text_range(
        func, file_source, issue_range_mode
    )
    comp = component_key(project_key, func.rel_path)
    h = hashlib.md5()
    h.update((comp + "|" + func.qualname + f"|{func.lineno}|{complexity}").encode("utf-8"))
    issue_hash = h.hexdigest()
                                                
    flows: List[dict] = []
    flows_sum = 0
    try:
        tracer = ComplexityTracer(project_key, func.rel_path, func.name, file_source or "")
        tracer.run(func.node)
        flows = tracer.to_flows()
                                                                          
        for f in flows:
            loc = f.get("locations", [{}])[0]
            msg: str = loc.get("msg", "")
                                                                
            m = re.match(r"\+(\d+)", msg)
            if m:
                flows_sum += int(m.group(1))
    except Exception:
        flows = []

    return {
        "key": issue_hash,
        "rule": RULE_KEY,
        "severity": "MAJOR",                                                     
        "component": comp,
        "project": project_key,
        "line": start_line,
        "hash": issue_hash,
        "textRange": {
            "startLine": start_line,
            "endLine": end_line,
            "startOffset": start_offset,
            "endOffset": end_offset,
        },
                                                                
        "flows": flows,
                                                                                    
        "message": f"Cognitive Complexity of '{func.qualname}' is {complexity}",
        "cognitiveComplexity": complexity,
        "flowsSum": flows_sum,
        "delta": complexity - flows_sum,
        "function": func.qualname,
    }


def analyze_project(
    project_root: Path,
    min_complexity: int,
    major_threshold: int,
    critical_threshold: int,
    project_key: Optional[str] = None,
    issue_range_mode: str = "signature",
) -> dict:
    root = project_root.resolve()
    if not project_key:
        project_key = root.name

    issues: List[dict] = []
    effort_total = 0
    for py_file in walk_python_files(root):
                                                         
        try:
            source = py_file.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            source = py_file.read_text(encoding="latin-1", errors="ignore")

        for func in collect_functions(py_file, root):
            try:
                value = get_cognitive_complexity(func.node)
            except Exception:
                                                              
                continue
            if value < min_complexity:
                continue
            issue = make_issue(
                project_key, func, value, source, issue_range_mode=issue_range_mode
            )
            sev = compute_severity(value, major_threshold, critical_threshold)
            issue["severity"] = sev
            issues.append(issue)
                                                           
            effort_total += max(0, value - min_complexity)

    total = len(issues)
    page_index = 1
    page_size = max(1, total)
    result = {
        "total": total,
        "p": page_index,
        "ps": page_size,
        "paging": {
            "pageIndex": page_index,
            "pageSize": page_size,
            "total": total,
        },
        "effortTotal": effort_total,
        "issues": issues,
    }
    return result


def parse_args(argv: Optional[List[str]] = None) -> argparse.Namespace:
    p = argparse.ArgumentParser(
        description=(
            "Analiza la complejidad cognitiva de funciones en un proyecto Python y emite un JSON estilo Sonar."
        )
    )
    p.add_argument(
        "--project",
        required=True,
        help="Ruta al proyecto Python a analizar",
    )
    p.add_argument(
        "--output",
        default="resultados.json",
        help="Ruta del archivo .json de salida (default: resultados.json)",
    )
    p.add_argument(
        "--min-complexity",
        type=int,
        default=15,
        help="Umbral mínimo de complejidad para reportar una función (default: 15)",
    )
    p.add_argument(
        "--major-threshold",
        type=int,
        default=15,
        help="Umbral para severidad MAJOR (default: 15)",
    )
    p.add_argument(
        "--critical-threshold",
        type=int,
        default=25,
        help="Umbral para severidad CRITICAL (default: 25)",
    )
    p.add_argument(
        "--project-key",
        help="Clave de proyecto a usar en 'component' y 'project' (default: nombre de la carpeta)",
    )
    p.add_argument(
        "--issue-range",
        choices=["keyword", "signature", "body"],
        default="body",
        help=(
            "Cómo calcular el textRange del issue: 'keyword' (def), 'signature' (nombre de la función), 'body' (todo el cuerpo; default)"
        ),
    )
    p.add_argument(
        "--force",
        action="store_true",
        help="Sobrescribe el archivo de salida si ya existe",
    )
    return p.parse_args(argv)


def main(argv: Optional[List[str]] = None) -> int:
    args = parse_args(argv)
    project_root = Path(args.project)
    if not project_root.exists():
        print(f"No existe la ruta de proyecto: {project_root}", file=sys.stderr)
        return 2

    result = analyze_project(
        project_root=project_root,
        min_complexity=args.min_complexity,
        major_threshold=args.major_threshold,
        critical_threshold=args.critical_threshold,
        project_key=args.project_key,
        issue_range_mode=args.issue_range,
    )
    out_path = Path(args.output)
    if out_path.exists() and not args.force:
        print(
            f"El archivo de salida ya existe: {out_path}. Usa --force o cambia --output.",
            file=sys.stderr,
        )
        return 3
    out_path.write_text(json.dumps(result, ensure_ascii=False, indent=2), encoding="utf-8")
    print(f"Archivo generado: {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
