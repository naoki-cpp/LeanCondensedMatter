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


def main() -> None:
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(
        json.dumps(export_modules(), indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


if __name__ == "__main__":
    main()
