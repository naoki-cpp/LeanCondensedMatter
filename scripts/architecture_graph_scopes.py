from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path

from architecture_audit_common import (
    ArchitectureEdge,
    ArchitectureGraph,
    ArchitectureLayer,
    check_architecture_graph_imports,
    lean_imports,
    module_matches_prefix,
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
    """Apply every scoped DAG to its declared source roots independently."""
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

            # The common graph validator short-circuits on an already-populated error list. Give
            # every scoped graph a fresh diagnostic buffer so an earlier failure never suppresses
            # validation or import diagnostics for later graphs.
            graph_errors: list[str] = []
            check_architecture_graph_imports(
                graph_errors,
                scoped.graph,
                root=root,
                source_root=source_root,
            )
            errors.extend(f"scoped graph `{scoped.id}`: {error}" for error in graph_errors)


def project_module_path(root: Path, module: str) -> Path | None:
    """Resolve a LeanCondensedMatter module to a source file when it is repository-owned."""
    prefix = "LeanCondensedMatter."
    if not module.startswith(prefix):
        return None
    path = root / "LeanCondensedMatter" / (module[len(prefix):].replace(".", "/") + ".lean")
    return path if path.is_file() else None


def check_forbidden_reachability_contracts(
    errors: list[str], spec_path: Path, *, root: Path
) -> None:
    """Reject transitive import paths from declared roots into forbidden module prefixes."""
    try:
        raw = json.loads(spec_path.read_text(encoding="utf-8"))
    except (OSError, TypeError, ValueError, json.JSONDecodeError) as error:
        errors.append(f"invalid reachability architecture specification: {error}")
        return

    seen_ids: set[str] = set()
    for contract in raw.get("forbiddenReachability", []):
        contract_id = contract["id"]
        if contract_id in seen_ids:
            errors.append(f"duplicate reachability contract id `{contract_id}`")
            continue
        seen_ids.add(contract_id)

        roots = tuple(contract["roots"])
        forbidden = tuple(contract["forbiddenPrefixes"])

        for start in roots:
            stack: list[tuple[str, tuple[str, ...]]] = [(start, (start,))]
            visited: set[str] = set()
            while stack:
                module, chain = stack.pop()
                if module in visited:
                    continue
                visited.add(module)

                source_path = project_module_path(root, module)
                if source_path is None:
                    errors.append(
                        f"reachability contract `{contract_id}` has missing project root module `{module}`"
                    )
                    continue

                for imported in lean_imports(source_path):
                    next_chain = (*chain, imported)
                    if any(module_matches_prefix(imported, prefix) for prefix in forbidden):
                        errors.append(
                            f"reachability contract `{contract_id}`: " + " -> ".join(next_chain)
                        )
                        continue
                    if project_module_path(root, imported) is not None:
                        stack.append((imported, next_chain))
