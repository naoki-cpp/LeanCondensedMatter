from __future__ import annotations

from pathlib import Path

from architecture_audit_common import (
    ArchitectureGraph,
    check_architecture_graph_imports,
    check_lean_import_syntax,
    finish_audit,
    load_architecture_graph,
    module_matches_prefix,
    repository_root,
)
from architecture_graph_scopes import (
    check_forbidden_reachability_contracts,
    check_scoped_import_graphs,
    validate_architecture_spec,
)

ROOT = repository_root(__file__)
LEAN = ROOT / "LeanCondensedMatter"
ARCHITECTURE = ROOT / "scripts" / "architecture"
SECOND_QUANTIZATION_SPEC = ARCHITECTURE / "second_quantization.json"
SOURCE_TOPOLOGY_SPEC = ARCHITECTURE / "source_topology.json"
AHE_TOPOLOGY_SPEC = ARCHITECTURE / "ahe_topology.json"
SCOPED_SPECS = (SECOND_QUANTIZATION_SPEC, SOURCE_TOPOLOGY_SPEC, AHE_TOPOLOGY_SPEC)


def check_primary_prefix_partition(errors: list[str], graph: ArchitectureGraph) -> None:
    """Keep Python longest-prefix and Lean first-match classification equivalent for the shared graph."""
    prefixes = [
        (layer.id, prefix)
        for layer in graph.layers
        for prefix in layer.module_prefixes
    ]
    for index, (left_id, left) in enumerate(prefixes):
        for right_id, right in prefixes[index + 1 :]:
            if left_id == right_id:
                continue
            if module_matches_prefix(left, right) or module_matches_prefix(right, left):
                errors.append(
                    "primary graph module prefixes must form a non-overlapping partition so Python "
                    f"and Lean classify identically: `{left}` ({left_id}) overlaps `{right}` ({right_id})"
                )


def check_primary_graph(errors: list[str], graph: ArchitectureGraph) -> None:
    check_primary_prefix_partition(errors, graph)
    graph_errors: list[str] = []
    check_architecture_graph_imports(graph_errors, graph, root=ROOT, source_root=LEAN)
    errors.extend(f"primary graph: {error}" for error in graph_errors)


def main() -> int:
    errors: list[str] = []

    # Source topology depends on understanding every import command. Validate the parser's supported
    # syntax repository-wide before any graph is allowed to ignore an import-looking line.
    check_lean_import_syntax(errors, root=ROOT, source_root=LEAN)

    valid_specs: dict[Path, bool] = {}
    for spec in SCOPED_SPECS:
        valid_specs[spec] = validate_architecture_spec(
            errors,
            spec,
            require_primary=spec == SECOND_QUANTIZATION_SPEC,
        )

    if valid_specs[SECOND_QUANTIZATION_SPEC]:
        try:
            graph = load_architecture_graph(SECOND_QUANTIZATION_SPEC)
        except (OSError, KeyError, TypeError, ValueError) as error:
            errors.append(f"invalid primary architecture graph: {error}")
        else:
            check_primary_graph(errors, graph)

    for spec in SCOPED_SPECS:
        if not valid_specs[spec]:
            continue
        check_scoped_import_graphs(errors, spec, root=ROOT)
        check_forbidden_reachability_contracts(errors, spec, root=ROOT)

    return finish_audit(
        errors,
        failure_heading="Declarative architecture graph audit failed:",
        success_message="Declarative architecture graph audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
