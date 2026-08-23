from __future__ import annotations

import json
from pathlib import Path

from architecture_audit_common import finish_audit, lean_imports, repository_root

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


def check_required_directories(errors: list[str], raw: dict[str, object]) -> None:
    for contract in raw.get("requiredDirectories", []):
        contract_id = contract["id"]
        for relative in contract["paths"]:
            path = ROOT / relative
            if not path.is_dir():
                errors.append(f"source contract `{contract_id}` missing directory: {relative}")


def check_required_imports(errors: list[str], raw: dict[str, object]) -> None:
    for contract in raw.get("requiredImports", []):
        contract_id = contract["id"]
        relative = contract["path"]
        path = ROOT / relative
        if not path.is_file():
            errors.append(f"source contract `{contract_id}` missing import owner: {relative}")
            continue
        imports = set(lean_imports(path))
        for module in contract["modules"]:
            if module not in imports:
                errors.append(
                    f"source contract `{contract_id}`: {relative} must import `{module}`"
                )


def main() -> int:
    errors: list[str] = []
    try:
        raw = load_spec()
    except (OSError, TypeError, ValueError, json.JSONDecodeError) as error:
        errors.append(f"invalid source contract specification: {error}")
    else:
        check_required_files(errors, raw)
        check_required_directories(errors, raw)
        check_required_imports(errors, raw)

    return finish_audit(
        errors,
        failure_heading="Declarative source contract audit failed:",
        success_message="Declarative source contract audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
