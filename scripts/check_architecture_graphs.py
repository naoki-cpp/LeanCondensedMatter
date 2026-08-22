from __future__ import annotations

from pathlib import Path

from architecture_audit_common import (
    ArchitectureGraph,
    check_architecture_graph_imports,
    finish_audit,
    load_architecture_graph,
    repository_root,
)
from architecture_graph_scopes import check_scoped_import_graphs

ROOT = repository_root(__file__)
LEAN = ROOT / "LeanCondensedMatter"
ARCHITECTURE = ROOT / "scripts" / "architecture"
SECOND_QUANTIZATION_SPEC = ARCHITECTURE / "second_quantization.json"
SOURCE_TOPOLOGY_SPEC = ARCHITECTURE / "source_topology.json"


def check_primary_graph(errors: list[str], graph: ArchitectureGraph) -> None:
    check_architecture_graph_imports(errors, graph, root=ROOT, source_root=LEAN)


def main() -> int:
    errors: list[str] = []

    try:
        graph = load_architecture_graph(SECOND_QUANTIZATION_SPEC)
    except (OSError, KeyError, TypeError, ValueError) as error:
        errors.append(f"invalid primary architecture graph: {error}")
    else:
        check_primary_graph(errors, graph)

    for spec in (SECOND_QUANTIZATION_SPEC, SOURCE_TOPOLOGY_SPEC):
        check_scoped_import_graphs(errors, spec, root=ROOT)

    return finish_audit(
        errors,
        failure_heading="Declarative architecture graph audit failed:",
        success_message="Declarative architecture graph audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
