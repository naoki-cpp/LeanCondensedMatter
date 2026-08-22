from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path

from architecture_audit_common import (
    ArchitectureEdge,
    ArchitectureGraph,
    ArchitectureLayer,
    check_architecture_graph_imports,
)


@dataclass(frozen=True)
class ScopedImportGraph:
    """One independently-scoped import DAG from the shared architecture specification."""

    id: str
    source_roots: tuple[Path, ...]
    graph: ArchitectureGraph


def load_scoped_import_graphs(spec_path: Path, *, root: Path) -> tuple[ScopedImportGraph, ...]:
    """Load optional scoped import DAGs from the shared JSON specification."""
    raw = json.loads(spec_path.read_text(encoding="utf-8"))
    graphs: list[ScopedImportGraph] = []
    seen_ids: set[str] = set()

    for item in raw.get("scopedImportGraphs", []):
        graph_id = item["id"]
        if graph_id in seen_ids:
            raise ValueError(f"duplicate scoped architecture graph id `{graph_id}`")
        seen_ids.add(graph_id)

        layers = tuple(
            ArchitectureLayer(
                id=layer["id"],
                module_prefixes=tuple(layer["modulePrefixes"]),
                namespace_prefixes=(),
                forbidden_name_fragments=(),
            )
            for layer in item["layers"]
        )
        edges = tuple(
            ArchitectureEdge(upstream=edge["upstream"], downstream=edge["downstream"])
            for edge in item["edges"]
        )
        source_roots = tuple(root / source_root for source_root in item["sourceRoots"])
        graphs.append(
            ScopedImportGraph(
                id=graph_id,
                source_roots=source_roots,
                graph=ArchitectureGraph(
                    layers=layers,
                    edges=edges,
                    namespace_exceptions=(),
                ),
            )
        )

    return tuple(graphs)


def check_scoped_import_graphs(errors: list[str], spec_path: Path, *, root: Path) -> None:
    """Apply every scoped DAG to its declared source roots."""
    try:
        graphs = load_scoped_import_graphs(spec_path, root=root)
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError) as error:
        errors.append(f"invalid scoped architecture graph specification: {error}")
        return

    for scoped in graphs:
        for source_root in scoped.source_roots:
            if not source_root.is_dir():
                errors.append(
                    f"scoped architecture graph `{scoped.id}` has missing source root: "
                    f"{source_root.relative_to(root)}"
                )
                continue
            before = len(errors)
            check_architecture_graph_imports(
                errors,
                scoped.graph,
                root=root,
                source_root=source_root,
            )
            if len(errors) > before:
                errors[before:] = [
                    f"scoped graph `{scoped.id}`: {error}" for error in errors[before:]
                ]
