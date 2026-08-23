from __future__ import annotations

import json
import re
import sys
from collections.abc import Iterable, Iterator
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path

IMPORT_RE = re.compile(r"^\s*import\s+([^\s]+)\s*$")


@dataclass(frozen=True)
class ArchitectureLayer:
    """One vertex in a declarative architecture graph."""

    id: str
    module_prefixes: tuple[str, ...]
    namespace_prefixes: tuple[str, ...]
    forbidden_name_fragments: tuple[str, ...]


@dataclass(frozen=True)
class ArchitectureEdge:
    """One allowed dependency direction, oriented upstream -> downstream."""

    upstream: str
    downstream: str


@dataclass(frozen=True)
class NamespaceException:
    """One explicit compiled declaration namespace exception."""

    module_prefix: str
    declaration_prefix: str


@dataclass(frozen=True)
class ArchitectureGraph:
    """Shared declarative architecture data consumed by source and compiled audits."""

    layers: tuple[ArchitectureLayer, ...]
    edges: tuple[ArchitectureEdge, ...]
    namespace_exceptions: tuple[NamespaceException, ...]


def repository_root(script_file: str | Path) -> Path:
    """Return the repository root for a script stored directly under ``scripts/``."""
    return Path(script_file).resolve().parents[1]


def relative(root: Path, path: Path) -> str:
    """Render a repository-relative path for stable diagnostics."""
    return str(path.relative_to(root))


@lru_cache(maxsize=None)
def _matching_files(root: Path, pattern: str) -> tuple[Path, ...]:
    """Cache deterministic file discovery for the read-only lifetime of one audit process."""
    if not root.exists():
        return ()
    return tuple(sorted(root.rglob(pattern)))


def files_matching(root: Path, pattern: str) -> Iterator[Path]:
    """Yield matching files in deterministic repository order."""
    yield from _matching_files(root, pattern)


def lean_files(root: Path) -> Iterator[Path]:
    yield from files_matching(root, "*.lean")


@lru_cache(maxsize=None)
def _source_text(path: Path) -> str:
    """Read one source file once during the read-only architecture audit."""
    return path.read_text(encoding="utf-8")


def _strip_lean_comments(text: str) -> str:
    """Remove Lean comments for comment-aware source-topology checks."""
    out: list[str] = []
    i = 0
    depth = 0
    in_string = False
    escaped = False

    while i < len(text):
        ch = text[i]
        nxt = text[i + 1] if i + 1 < len(text) else ""

        if depth:
            if ch == "/" and nxt == "-":
                depth += 1
                out.extend("  ")
                i += 2
            elif ch == "-" and nxt == "/":
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue

        if in_string:
            out.append(ch)
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
            i += 1
            continue

        if ch == '"':
            in_string = True
            out.append(ch)
            i += 1
        elif ch == "/" and nxt == "-":
            depth = 1
            out.extend("  ")
            i += 2
        elif ch == "-" and nxt == "-":
            while i < len(text) and text[i] != "\n":
                out.append(" ")
                i += 1
        else:
            out.append(ch)
            i += 1

    return "".join(out)


@lru_cache(maxsize=None)
def lean_source(path: Path) -> str:
    """Return cached comment-stripped source for direct-import and narrow syntax checks."""
    return _strip_lean_comments(_source_text(path))


@lru_cache(maxsize=None)
def _numbered_imports(path: Path) -> tuple[tuple[int, str], ...]:
    imports: list[tuple[int, str]] = []
    for line_no, line in enumerate(lean_source(path).splitlines(), start=1):
        if match := IMPORT_RE.match(line):
            imports.append((line_no, match.group(1)))
    return tuple(imports)


def numbered_imports(path: Path) -> Iterator[tuple[int, str]]:
    """Yield cached direct Lean imports with source line numbers after removing comments."""
    yield from _numbered_imports(path)


@lru_cache(maxsize=None)
def lean_imports(path: Path) -> tuple[str, ...]:
    """Return cached direct Lean imports after removing comments."""
    return tuple(imported for _, imported in _numbered_imports(path))


def module_matches_prefix(module: str, prefix: str) -> bool:
    """Match a Lean module prefix without conflating siblings such as Foo and FooExtra."""
    return module == prefix or module.startswith(prefix + ".")


def require_files(
    errors: list[str],
    paths: Iterable[Path],
    *,
    root: Path,
    description: str,
) -> None:
    """Require canonical owner files to exist."""
    for path in paths:
        if not path.is_file():
            errors.append(f"missing {description}: {relative(root, path)}")


def require_import(
    errors: list[str],
    path: Path,
    imported: str,
    *,
    root: Path,
    description: str = "module",
) -> None:
    """Require one direct Lean import from an existing source file."""
    if not path.is_file():
        errors.append(f"missing {description}: {relative(root, path)}")
        return
    if imported not in lean_imports(path):
        errors.append(f"{relative(root, path)} must import `{imported}`")


def load_architecture_graph(path: Path) -> ArchitectureGraph:
    """Load a shared architecture graph from JSON without embedding checker logic in the spec."""
    raw = json.loads(path.read_text(encoding="utf-8"))
    layers = tuple(
        ArchitectureLayer(
            id=layer["id"],
            module_prefixes=tuple(layer["modulePrefixes"]),
            namespace_prefixes=tuple(layer["namespacePrefixes"]),
            forbidden_name_fragments=tuple(layer["forbiddenNameFragments"]),
        )
        for layer in raw["layers"]
    )
    edges = tuple(
        ArchitectureEdge(upstream=edge["upstream"], downstream=edge["downstream"])
        for edge in raw["edges"]
    )
    exceptions = tuple(
        NamespaceException(
            module_prefix=exception["modulePrefix"],
            declaration_prefix=exception["declarationPrefix"],
        )
        for exception in raw["namespaceExceptions"]
    )
    return ArchitectureGraph(layers=layers, edges=edges, namespace_exceptions=exceptions)


def architecture_layer_for_module(
    graph: ArchitectureGraph, module: str
) -> ArchitectureLayer | None:
    """Classify a module by the longest matching graph prefix."""
    matches: list[tuple[int, ArchitectureLayer]] = []
    for layer in graph.layers:
        for prefix in layer.module_prefixes:
            if module_matches_prefix(module, prefix):
                matches.append((len(prefix), layer))
    if not matches:
        return None
    longest = max(length for length, _ in matches)
    winners = {layer.id: layer for length, layer in matches if length == longest}
    if len(winners) != 1:
        raise ValueError(f"ambiguous architecture layer for module `{module}`: {sorted(winners)}")
    return next(iter(winners.values()))


def architecture_graph_reaches(graph: ArchitectureGraph, upstream: str, downstream: str) -> bool:
    """Return whether the DAG contains a nonempty upstream-to-downstream path."""
    stack = [upstream]
    seen = {upstream}
    while stack:
        current = stack.pop()
        for edge in graph.edges:
            if edge.upstream != current:
                continue
            if edge.downstream == downstream:
                return True
            if edge.downstream not in seen:
                seen.add(edge.downstream)
                stack.append(edge.downstream)
    return False


def validate_architecture_graph(errors: list[str], graph: ArchitectureGraph) -> None:
    """Validate graph identifiers, prefix ownership, and acyclicity before applying it."""
    ids = [layer.id for layer in graph.layers]
    if len(ids) != len(set(ids)):
        errors.append("architecture graph contains duplicate layer ids")
        return

    known = set(ids)
    for edge in graph.edges:
        if edge.upstream not in known or edge.downstream not in known:
            errors.append(
                f"architecture graph edge `{edge.upstream} -> {edge.downstream}` references an unknown layer"
            )

    prefix_owners: dict[str, str] = {}
    for layer in graph.layers:
        for prefix in layer.module_prefixes:
            previous = prefix_owners.setdefault(prefix, layer.id)
            if previous != layer.id:
                errors.append(
                    f"architecture module prefix `{prefix}` belongs to both `{previous}` and `{layer.id}`"
                )

    if errors:
        return
    for layer_id in ids:
        if architecture_graph_reaches(graph, layer_id, layer_id):
            errors.append(f"architecture graph contains a cycle through `{layer_id}`")


def module_name_from_path(root: Path, path: Path) -> str:
    """Convert a repository Lean source path into its module name."""
    rel = path.relative_to(root).with_suffix("")
    return ".".join(rel.parts)


def check_architecture_graph_imports(
    errors: list[str],
    graph: ArchitectureGraph,
    *,
    root: Path,
    source_root: Path,
) -> None:
    """Require each classified project import to point to the same layer or a graph ancestor."""
    validate_architecture_graph(errors, graph)
    if errors:
        return

    for path in lean_files(source_root):
        source_module = module_name_from_path(root, path)
        source_layer = architecture_layer_for_module(graph, source_module)
        if source_layer is None:
            continue
        for line_no, imported in numbered_imports(path):
            target_layer = architecture_layer_for_module(graph, imported)
            if target_layer is None or target_layer.id == source_layer.id:
                continue
            if architecture_graph_reaches(graph, target_layer.id, source_layer.id):
                continue
            errors.append(
                "architecture graph violation: "
                f"{relative(root, path)}:{line_no} `{source_layer.id}` imports `{imported}` "
                f"from non-ancestor layer `{target_layer.id}`"
            )


def finish_audit(
    errors: list[str],
    *,
    failure_heading: str,
    success_message: str,
) -> int:
    """Print diagnostics in the shared audit format and return a process status."""
    if errors:
        print(failure_heading, file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print(success_message)
    return 0
