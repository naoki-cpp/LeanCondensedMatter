from __future__ import annotations

import json
from collections import Counter

from architecture_audit_common import (
    finish_audit,
    lean_imports,
    module_matches_prefix,
    repository_root,
)

ROOT = repository_root(__file__)
SPEC = ROOT / "scripts" / "architecture" / "source_contracts.json"


def load_spec() -> dict[str, object]:
    return json.loads(SPEC.read_text(encoding="utf-8"))


def check_required_files(errors: list[str], raw: dict[str, object]) -> None:
    for contract in raw.get("requiredFiles", []):
        contract_id = contract["id"]
        for relative in contract["paths"]:
            path = ROOT / relative
            if not path.is_file():
                errors.append(f"source contract `{contract_id}` missing file: {relative}")


def check_forbidden_files(errors: list[str], raw: dict[str, object]) -> None:
    for contract in raw.get("forbiddenFiles", []):
        contract_id = contract["id"]
        for relative in contract["paths"]:
            if (ROOT / relative).exists():
                errors.append(f"source contract `{contract_id}` forbids retired path: {relative}")


def check_required_directories(errors: list[str], raw: dict[str, object]) -> None:
    for contract in raw.get("requiredDirectories", []):
        contract_id = contract["id"]
        for relative in contract["paths"]:
            path = ROOT / relative
            if not path.is_dir():
                errors.append(f"source contract `{contract_id}` missing directory: {relative}")


def imports_for_contract(errors: list[str], contract_id: str, relative: str) -> tuple[str, ...] | None:
    path = ROOT / relative
    if not path.is_file():
        errors.append(f"source contract `{contract_id}` missing import owner: {relative}")
        return None
    return lean_imports(path)


def check_required_imports(errors: list[str], raw: dict[str, object]) -> None:
    for contract in raw.get("requiredImports", []):
        contract_id = contract["id"]
        relative = contract["path"]
        imports = imports_for_contract(errors, contract_id, relative)
        if imports is None:
            continue
        imported_set = set(imports)
        for module in contract["modules"]:
            if module not in imported_set:
                errors.append(
                    f"source contract `{contract_id}`: {relative} must import `{module}`"
                )


def check_exact_imports(errors: list[str], raw: dict[str, object]) -> None:
    for contract in raw.get("exactImports", []):
        contract_id = contract["id"]
        relative = contract["path"]
        imports = imports_for_contract(errors, contract_id, relative)
        if imports is None:
            continue
        expected = set(contract["modules"])
        actual = set(imports)
        counts = Counter(imports)
        for module in sorted(expected - actual):
            errors.append(f"source contract `{contract_id}`: {relative} is missing `{module}`")
        for module in sorted(actual - expected):
            errors.append(f"source contract `{contract_id}`: {relative} imports unexpected `{module}`")
        for module, count in sorted(counts.items()):
            if count > 1:
                errors.append(
                    f"source contract `{contract_id}`: {relative} imports `{module}` {count} times"
                )


def check_forbidden_imports(errors: list[str], raw: dict[str, object]) -> None:
    for contract in raw.get("forbiddenImports", []):
        contract_id = contract["id"]
        relative = contract["path"]
        imports = imports_for_contract(errors, contract_id, relative)
        if imports is None:
            continue
        for module in contract["modules"]:
            if module in imports:
                errors.append(
                    f"source contract `{contract_id}`: {relative} must not import `{module}`"
                )


def check_forbidden_import_prefixes(errors: list[str], raw: dict[str, object]) -> None:
    for contract in raw.get("forbiddenImportPrefixes", []):
        contract_id = contract["id"]
        relative = contract["path"]
        imports = imports_for_contract(errors, contract_id, relative)
        if imports is None:
            continue
        for imported in imports:
            for prefix in contract["prefixes"]:
                if module_matches_prefix(imported, prefix):
                    errors.append(
                        f"source contract `{contract_id}`: {relative} must not import `{imported}` "
                        f"from forbidden prefix `{prefix}`"
                    )


def main() -> int:
    errors: list[str] = []
    try:
        raw = load_spec()
    except (OSError, TypeError, ValueError, json.JSONDecodeError) as error:
        errors.append(f"invalid source contract specification: {error}")
    else:
        check_required_files(errors, raw)
        check_forbidden_files(errors, raw)
        check_required_directories(errors, raw)
        check_required_imports(errors, raw)
        check_exact_imports(errors, raw)
        check_forbidden_imports(errors, raw)
        check_forbidden_import_prefixes(errors, raw)

    return finish_audit(
        errors,
        failure_heading="Declarative source contract audit failed:",
        success_message="Declarative source contract audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
