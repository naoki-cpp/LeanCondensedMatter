"""Export the project Lean modules and their direct imports for the documentation site."""

from __future__ import annotations

import json
from pathlib import Path

from architecture_audit_common import lean_files, lean_imports, module_name_from_path


ROOT = Path(__file__).resolve().parents[1]
SOURCE_ROOT = ROOT / "LeanCondensedMatter"
PROJECT_PREFIX = "LeanCondensedMatter."
OUTPUT = ROOT / "docs" / "generated" / "module-imports.json"


def is_project_module(name: str) -> bool:
    return name == "LeanCondensedMatter" or name.startswith(PROJECT_PREFIX)


def export_modules() -> dict[str, object]:
    source_files = list(lean_files(SOURCE_ROOT))
    root_module = ROOT / "LeanCondensedMatter.lean"
    if root_module.is_file():
        source_files.append(root_module)
    modules: list[dict[str, object]] = []
    for source_file in sorted(source_files):
        name = module_name_from_path(ROOT, source_file)
        imports = sorted(set(lean_imports(source_file)))
        modules.append(
            {
                "name": name,
                "sourceFile": source_file.relative_to(ROOT).as_posix(),
                "imports": [module for module in imports if is_project_module(module)],
                "externalImportCount": sum(not is_project_module(module) for module in imports),
            }
        )
    return {"modules": modules}


def import_overlap_candidates(modules: list[dict[str, object]]) -> list[tuple[str, str, str]]:
    """Report project-local direct imports also reachable through another direct import.

    Reachability is only a triage signal, not evidence that a direct import can be
    removed in Lean's module system or that its visibility can be changed.
    """
    graph = {entry["name"]: tuple(entry["imports"]) for entry in modules}
    reachable_cache: dict[str, set[str]] = {}

    def reachable_from(module: str) -> set[str]:
        if module not in reachable_cache:
            seen: set[str] = set()
            remaining = list(graph.get(module, ()))
            while remaining:
                imported = remaining.pop()
                if imported in seen:
                    continue
                seen.add(imported)
                remaining.extend(graph.get(imported, ()))
            reachable_cache[module] = seen
        return reachable_cache[module]

    candidates: list[tuple[str, str, str]] = []
    for entry in sorted(modules, key=lambda item: item["name"]):
        direct_imports = graph[entry["name"]]
        for target in direct_imports:
            for via in direct_imports:
                if via != target and target in reachable_from(via):
                    candidates.append((entry["sourceFile"], target, via))
                    break
    return candidates


def is_module_system_file(relative_path: str) -> bool:
    from architecture_audit_common import lean_source

    source = lean_source(ROOT / relative_path).lstrip().splitlines()
    return bool(source and source[0].strip() == "module")


def main() -> None:
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--report-overlaps",
        action="store_true",
        help="Print advisory transitive overlaps between project-local direct imports",
    )
    parser.add_argument(
        "--limit",
        type=int,
        default=30,
        help="Maximum overlap candidates to show (default: 30)",
    )
    args = parser.parse_args()
    if args.limit < 0:
        parser.error("--limit must be nonnegative")

    inventory = export_modules()
    if args.report_overlaps:
        candidates = import_overlap_candidates(inventory["modules"])
        module_system = {
            path: is_module_system_file(path) for path, _, _ in candidates
        }
        candidates.sort(
            key=lambda candidate: (
                not module_system[candidate[0]],
                candidate[0],
                candidate[1],
                candidate[2],
            )
        )
        print(f"{len(candidates)} project-local transitive import overlap(s) (advisory only)")
        for path, target, via in candidates[:args.limit]:
            flavor = "module" if module_system[path] else "legacy"
            print(f"[{flavor}] {path}: `{target}` also reachable via `{via}`")
        if len(candidates) > args.limit:
            print(f"... {len(candidates) - args.limit} more; increase --limit to see them")
        print("Do not remove direct imports without checking Lean module visibility and compilation.")
        return

    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(
        json.dumps(inventory, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


if __name__ == "__main__":
    main()
