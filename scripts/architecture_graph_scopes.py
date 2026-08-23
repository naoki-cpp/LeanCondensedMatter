from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path

from architecture_audit_common import (
    ArchitectureEdge,
    ArchitectureGraph,
    ArchitectureLayer,
    architecture_layer_for_module,
    check_architecture_graph_imports,
    lean_files,
    lean_imports,
    module_matches_prefix,
    module_name_from_path,
)

TOP_LEVEL_FIELDS = {
    "layers",
    "edges",
    "namespaceExceptions",
    "scopedImportGraphs",
    "forbiddenReachability",
}
PRIMARY_FIELDS = {"layers", "edges", "namespaceExceptions"}


@dataclass(frozen=True)
class ScopedImportGraph:
    """One independently-scoped import DAG from the shared architecture specification."""

    id: str
    source_roots: tuple[Path, ...]
    coverage_prefixes: tuple[str, ...]
    graph: ArchitectureGraph


def _validate_object_fields(
    errors: list[str],
    *,
    context: str,
    value: object,
    required: set[str],
    optional: set[str] | None = None,
) -> dict[str, object] | None:
    if not isinstance(value, dict):
        errors.append(f"{context} must be an object")
        return None
    optional = optional or set()
    missing = sorted(required - set(value))
    unknown = sorted(set(value) - required - optional)
    if missing:
        errors.append(f"{context} is missing fields: {', '.join(missing)}")
    if unknown:
        errors.append(f"{context} has unknown fields: {', '.join(unknown)}")
    return value


def _validate_string(errors: list[str], *, context: str, value: object) -> None:
    if not isinstance(value, str) or not value:
        errors.append(f"{context} must be a nonempty string")


def _validate_string_list(
    errors: list[str],
    *,
    context: str,
    value: object,
    allow_empty: bool = False,
) -> None:
    if not isinstance(value, list) or not all(isinstance(item, str) and item for item in value):
        errors.append(f"{context} must be a list of nonempty strings")
        return
    if not allow_empty and not value:
        errors.append(f"{context} must not be empty")


def _validate_edge_list(errors: list[str], *, context: str, value: object) -> None:
    if not isinstance(value, list):
        errors.append(f"{context} must be a list")
        return
    seen: set[tuple[str, str]] = set()
    for index, raw_edge in enumerate(value):
        edge_context = f"{context}[{index}]"
        edge = _validate_object_fields(
            errors,
            context=edge_context,
            value=raw_edge,
            required={"upstream", "downstream"},
        )
        if edge is None or "upstream" not in edge or "downstream" not in edge:
            continue
        _validate_string(errors, context=f"{edge_context}.upstream", value=edge["upstream"])
        _validate_string(errors, context=f"{edge_context}.downstream", value=edge["downstream"])
        if isinstance(edge["upstream"], str) and isinstance(edge["downstream"], str):
            key = (edge["upstream"], edge["downstream"])
            if key in seen:
                errors.append(
                    f"{context} contains duplicate edge `{edge['upstream']} -> {edge['downstream']}`"
                )
            seen.add(key)


def _validate_primary_graph(errors: list[str], raw: dict[str, object], *, context: str) -> None:
    layers = raw.get("layers")
    if not isinstance(layers, list):
        errors.append(f"{context}.layers must be a list")
    else:
        for index, raw_layer in enumerate(layers):
            layer_context = f"{context}.layers[{index}]"
            layer = _validate_object_fields(
                errors,
                context=layer_context,
                value=raw_layer,
                required={"id", "modulePrefixes", "namespacePrefixes", "forbiddenNameFragments"},
            )
            if layer is None:
                continue
            for field in ("id",):
                if field in layer:
                    _validate_string(errors, context=f"{layer_context}.{field}", value=layer[field])
            for field in ("modulePrefixes", "namespacePrefixes", "forbiddenNameFragments"):
                if field in layer:
                    _validate_string_list(
                        errors,
                        context=f"{layer_context}.{field}",
                        value=layer[field],
                        allow_empty=field != "modulePrefixes",
                    )

    _validate_edge_list(errors, context=f"{context}.edges", value=raw.get("edges"))

    exceptions = raw.get("namespaceExceptions")
    if not isinstance(exceptions, list):
        errors.append(f"{context}.namespaceExceptions must be a list")
    else:
        for index, raw_exception in enumerate(exceptions):
            exception_context = f"{context}.namespaceExceptions[{index}]"
            exception = _validate_object_fields(
                errors,
                context=exception_context,
                value=raw_exception,
                required={"modulePrefix", "declarationPrefix"},
            )
            if exception is None:
                continue
            for field in ("modulePrefix", "declarationPrefix"):
                if field in exception:
                    _validate_string(
                        errors,
                        context=f"{exception_context}.{field}",
                        value=exception[field],
                    )


def _validate_scoped_graphs(
    errors: list[str], raw: dict[str, object], *, context: str, seen_ids: set[str]
) -> None:
    graphs = raw.get("scopedImportGraphs", [])
    if not isinstance(graphs, list):
        errors.append(f"{context}.scopedImportGraphs must be a list")
        return

    for index, raw_graph in enumerate(graphs):
        graph_context = f"{context}.scopedImportGraphs[{index}]"
        graph = _validate_object_fields(
            errors,
            context=graph_context,
            value=raw_graph,
            required={"id", "sourceRoots", "layers", "edges"},
            optional={"coveragePrefixes"},
        )
        if graph is None:
            continue

        graph_id = graph.get("id")
        _validate_string(errors, context=f"{graph_context}.id", value=graph_id)
        if isinstance(graph_id, str) and graph_id:
            if graph_id in seen_ids:
                errors.append(f"duplicate architecture contract id `{graph_id}`")
            seen_ids.add(graph_id)

        if "sourceRoots" in graph:
            _validate_string_list(
                errors, context=f"{graph_context}.sourceRoots", value=graph["sourceRoots"]
            )
        if "coveragePrefixes" in graph:
            _validate_string_list(
                errors,
                context=f"{graph_context}.coveragePrefixes",
                value=graph["coveragePrefixes"],
            )

        layers = graph.get("layers")
        if not isinstance(layers, list) or not layers:
            errors.append(f"{graph_context}.layers must be a nonempty list")
        else:
            for layer_index, raw_layer in enumerate(layers):
                layer_context = f"{graph_context}.layers[{layer_index}]"
                layer = _validate_object_fields(
                    errors,
                    context=layer_context,
                    value=raw_layer,
                    required={"id", "modulePrefixes"},
                )
                if layer is None:
                    continue
                if "id" in layer:
                    _validate_string(errors, context=f"{layer_context}.id", value=layer["id"])
                if "modulePrefixes" in layer:
                    _validate_string_list(
                        errors,
                        context=f"{layer_context}.modulePrefixes",
                        value=layer["modulePrefixes"],
                    )

        _validate_edge_list(errors, context=f"{graph_context}.edges", value=graph.get("edges"))


def _validate_reachability(
    errors: list[str], raw: dict[str, object], *, context: str, seen_ids: set[str]
) -> None:
    contracts = raw.get("forbiddenReachability", [])
    if not isinstance(contracts, list):
        errors.append(f"{context}.forbiddenReachability must be a list")
        return

    for index, raw_contract in enumerate(contracts):
        contract_context = f"{context}.forbiddenReachability[{index}]"
        contract = _validate_object_fields(
            errors,
            context=contract_context,
            value=raw_contract,
            required={"id", "roots", "forbiddenPrefixes"},
        )
        if contract is None:
            continue

        contract_id = contract.get("id")
        _validate_string(errors, context=f"{contract_context}.id", value=contract_id)
        if isinstance(contract_id, str) and contract_id:
            if contract_id in seen_ids:
                errors.append(f"duplicate architecture contract id `{contract_id}`")
            seen_ids.add(contract_id)
        for field in ("roots", "forbiddenPrefixes"):
            if field in contract:
                _validate_string_list(
                    errors,
                    context=f"{contract_context}.{field}",
                    value=contract[field],
                )


def validate_architecture_spec(
    errors: list[str], spec_path: Path, *, require_primary: bool = False
) -> bool:
    """Validate the JSON schema strictly so misspelled contracts cannot silently disappear."""
    context = spec_path.name
    start = len(errors)
    try:
        raw = json.loads(spec_path.read_text(encoding="utf-8"))
    except (OSError, TypeError, ValueError, json.JSONDecodeError) as error:
        errors.append(f"{context}: invalid architecture specification: {error}")
        return False
    if not isinstance(raw, dict):
        errors.append(f"{context}: architecture specification must be an object")
        return False

    unknown = sorted(set(raw) - TOP_LEVEL_FIELDS)
    if unknown:
        errors.append(f"{context}: unknown top-level fields: {', '.join(unknown)}")

    present_primary = PRIMARY_FIELDS & set(raw)
    if require_primary:
        missing = sorted(PRIMARY_FIELDS - set(raw))
        if missing:
            errors.append(f"{context}: missing primary graph fields: {', '.join(missing)}")
    elif present_primary and present_primary != PRIMARY_FIELDS:
        missing = sorted(PRIMARY_FIELDS - set(raw))
        errors.append(f"{context}: incomplete primary graph fields: {', '.join(missing)}")

    if PRIMARY_FIELDS <= set(raw):
        _validate_primary_graph(errors, raw, context=context)

    seen_ids: set[str] = set()
    _validate_scoped_graphs(errors, raw, context=context, seen_ids=seen_ids)
    _validate_reachability(errors, raw, context=context, seen_ids=seen_ids)
    return len(errors) == start


def load_scoped_import_graphs(spec_path: Path, *, root: Path) -> tuple[ScopedImportGraph, ...]:
    """Load optional scoped import DAGs from a validated shared JSON specification."""
    raw = json.loads(spec_path.read_text(encoding="utf-8"))
    graphs: list[ScopedImportGraph] = []

    for item in raw.get("scopedImportGraphs", []):
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
                id=item["id"],
                source_roots=source_roots,
                coverage_prefixes=tuple(item.get("coveragePrefixes", [])),
                graph=ArchitectureGraph(
                    layers=layers,
                    edges=edges,
                    namespace_exceptions=(),
                ),
            )
        )

    return tuple(graphs)


def check_scoped_graph_coverage(errors: list[str], scoped: ScopedImportGraph, *, root: Path) -> None:
    """Require covered source modules to belong to a declared scoped-DAG layer."""
    if not scoped.coverage_prefixes:
        return

    matched_prefixes: set[str] = set()
    checked_paths: set[Path] = set()
    for source_root in scoped.source_roots:
        if not source_root.is_dir():
            continue
        for path in lean_files(source_root):
            if path in checked_paths:
                continue
            checked_paths.add(path)
            module = module_name_from_path(root, path)
            matching = [
                prefix
                for prefix in scoped.coverage_prefixes
                if module_matches_prefix(module, prefix)
            ]
            if not matching:
                continue
            matched_prefixes.update(matching)
            if architecture_layer_for_module(scoped.graph, module) is None:
                errors.append(
                    f"scoped graph `{scoped.id}` coverage: `{module}` is not assigned to any layer"
                )

    for prefix in scoped.coverage_prefixes:
        if prefix not in matched_prefixes:
            errors.append(
                f"scoped graph `{scoped.id}` coverage prefix `{prefix}` matches no source module"
            )


def check_scoped_import_graphs(errors: list[str], spec_path: Path, *, root: Path) -> None:
    """Apply every scoped DAG to its declared source roots independently."""
    try:
        graphs = load_scoped_import_graphs(spec_path, root=root)
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError) as error:
        errors.append(f"invalid scoped architecture graph specification: {error}")
        return

    for scoped in graphs:
        check_scoped_graph_coverage(errors, scoped, root=root)
        for source_root in scoped.source_roots:
            if not source_root.is_dir():
                errors.append(
                    f"scoped architecture graph `{scoped.id}` has missing source root: "
                    f"{source_root.relative_to(root)}"
                )
                continue

            # Give every scoped graph a fresh diagnostic buffer so an earlier failure never
            # suppresses validation or import diagnostics for later graphs.
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

    for contract in raw.get("forbiddenReachability", []):
        contract_id = contract["id"]
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
