from __future__ import annotations

from pathlib import Path

from architecture_audit_common import finish_audit, lean_imports, relative as relative_to, repository_root

ROOT = repository_root(__file__)
SQ = ROOT / "LeanCondensedMatter" / "SecondQuantization"
SECOND_QUANTIZATION = "LeanCondensedMatter.SecondQuantization"


def relative(path: Path) -> str:
    return relative_to(ROOT, path)


def check_entry_point(errors: list[str]) -> None:
    entry = SQ.with_suffix(".lean")
    if not entry.is_file():
        errors.append(f"missing canonical entry point: {relative(entry)}")

    root_module = ROOT / "LeanCondensedMatter.lean"
    if SECOND_QUANTIZATION not in lean_imports(root_module):
        errors.append(
            "repository root does not import canonical entry point: "
            f"{SECOND_QUANTIZATION}"
        )


def main() -> int:
    errors: list[str] = []
    check_entry_point(errors)
    return finish_audit(
        errors,
        failure_heading="SecondQuantization architecture audit failed:",
        success_message="SecondQuantization architecture audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
