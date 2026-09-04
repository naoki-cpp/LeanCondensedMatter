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

CONTRACT_FIELDS = {
    "requiredFiles": ("id", "paths"),
    # Kept parseable until the data file is cleaned up, but intentionally not enforced: CI should
    # protect current architecture, not remember that retired paths must stay absent forever.
    "forbiddenFiles": ("id", "paths"),
    "requiredDirectories": ("id", "paths"),
    "requiredImports": ("id", "path", "modules"),
    "exactImports": ("id", "path", "modules"),
    "forbiddenImports": ("id", "path", "modules"),
    "forbiddenImportPrefixes": ("id", "path", "prefixes"),
}


def load_spec() -> dict[str, object]:
    raw = json.loads(SPEC.read_text(encoding="utf-8"))
    if not isinstance(raw, dict):
        raise ValueError("source contract specification must be a JSON object")
    return raw


def validate_string_list(
    errors: list[str], category: str, contract_id: str, field: str, value: object
) -> None:
    if not isinstance(value, list) or not all(isinstance(item, str) and item for item in value):
        errors.append(
            f"source contract `{contract_id}` in `{category}` requires `{field}` to be a list of nonempty strings"
        )


def validate_spec(errors: list[str], raw: dict[str, object]) -> None:
    unknown = sorted(set(raw) - set(CONTRACT_FIELDS))
    for key in unknown:
        errors.append(f"unknown source contract category `{key}`")

    seen_ids: set[str] = set()
    for category, required_fields in CONTRACT_FIELDS.items():
        contracts = raw.get(category, [])
        if not isinstance(contracts, list):
            errors.append(f"source contract category `{category}` must be a list")
            continue
        for index, contract in enumerate(contracts):
            if not isinstance(contract, dict):
                errors.append(f"source contract `{category}` item {index} must be an object")
                continue
            missing = [field for field in required_fields if field not in contract]
            extra = sorted(set(contract) - set(required_fields))
            if missing:
                errors.append(
                    f"source contract `{category}` item {index} is missing fields: {', '.join(missing)}"
                )
            if extra:
                errors.append(
                    f"source contract `{category}` item {index} has unknown fields: {', '.join(extra)}"
                )
            if missing:
                continue

            contract_id = contract["id"]
            if not isinstance(contract_id, str) or not contract_id:
                errors.append(f"source contract `{category}` item {index} has invalid `id`")
                continue
            if contract_id in seen_ids:
                errors.append(f"duplicate source contract id `{contract_id}`")
            seen_ids.add(contract_id)

            if "path" in required_fields:
                path = contract["path"]
                if not isinstance(path, str) or not path:
                    errors.append(f"source contract `{contract_id}` requires a nonempty `path`")
            for field in ("paths", "modules", "prefixes"):
                if field in required_fields:
                    validate_string_list(errors, category, contract_id, field, contract[field])


def check_required_files(errors: list[str], raw: dict[str, object]) -> None:
    for contract in raw.get("requiredFiles", []):
        contract_id = contract["id"]
        for relative in contract["paths"]:
            path = ROOT / relative
            if not path.is_file():
                errors.append(f"source contract `{contract_id}` missing file: {relative}")


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
        validate_spec(errors, raw)
        if not errors:
            check_required_files(errors, raw)
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
