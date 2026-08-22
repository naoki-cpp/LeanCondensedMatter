from __future__ import annotations

from pathlib import Path

from architecture_audit_common import (
    ArchitectureGraph,
    check_architecture_graph_imports,
    finish_audit,
    lean_imports,
    load_architecture_graph,
    relative as relative_to,
    repository_root,
)
from architecture_graph_scopes import check_scoped_import_graphs

ROOT = repository_root(__file__)
LEAN = ROOT / "LeanCondensedMatter"
SQ = LEAN / "SecondQuantization"
GRAPH_SPEC = ROOT / "scripts" / "architecture" / "second_quantization.json"
SECOND_QUANTIZATION = "LeanCondensedMatter.SecondQuantization"


def relative(path: Path) -> str:
    return relative_to(ROOT, path)


def check_dependency_graph(errors: list[str], graph: ArchitectureGraph) -> None:
    check_architecture_graph_imports(errors, graph, root=ROOT, source_root=LEAN)
    check_scoped_import_graphs(errors, GRAPH_SPEC, root=ROOT)


def check_entry_point(errors: list[str]) -> None:
    entry = SQ.with_suffix(".lean")
    if not entry.is_file():
        errors.append(f"missing canonical entry point: {relative(entry)}")

    root_module = ROOT / "LeanCondensedMatter.lean"
    if SECOND_QUANTIZATION not in lean_imports(root_module):
        errors.append(
            "repository root does not import canonical entry point: "
            f"{SECOND_QUANTIZATION}"
        )


def main() -> int:
    errors: list[str] = []
    try:
        graph = load_architecture_graph(GRAPH_SPEC)
    except (OSError, KeyError, TypeError, ValueError) as error:
        errors.append(f"invalid SecondQuantization architecture graph: {error}")
        return finish_audit(
            errors,
            failure_heading="SecondQuantization architecture audit failed:",
            success_message="SecondQuantization architecture audit passed.",
        )

    check_dependency_graph(errors, graph)
    check_entry_point(errors)
    return finish_audit(
        errors,
        failure_heading="SecondQuantization architecture audit failed:",
        success_message="SecondQuantization architecture audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
