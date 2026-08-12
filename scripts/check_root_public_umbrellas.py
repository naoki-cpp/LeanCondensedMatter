from __future__ import annotations

from pathlib import Path

from architecture_audit_common import finish_audit, repository_root, strip_lean_comments

ROOT = repository_root(__file__)
ROOT_MODULE = ROOT / "LeanCondensedMatter.lean"
LEAN_ROOT = ROOT / "LeanCondensedMatter"

PUBLIC_TRACK_IMPORTS = (
    "LeanCondensedMatter.Analysis",
    "LeanCondensedMatter.Combinatorics",
    "LeanCondensedMatter.Permutation",
    "LeanCondensedMatter.QuantumTheory",
    "LeanCondensedMatter.QuantumMechanics",
    "LeanCondensedMatter.Transport",
    "LeanCondensedMatter.SecondQuantization",
)


def check_root_imports(errors: list[str]) -> None:
    if not ROOT_MODULE.is_file():
        errors.append("missing project root module: LeanCondensedMatter.lean")
        return

    code = strip_lean_comments(ROOT_MODULE.read_text(encoding="utf-8"))
    imports = [
        line.strip().removeprefix("import ").strip()
        for line in code.splitlines()
        if line.strip().startswith("import ")
    ]

    expected = list(PUBLIC_TRACK_IMPORTS)
    if imports != expected:
        errors.append(
            "LeanCondensedMatter.lean must import only the canonical public track umbrellas in "
            "their stable order; found: " + ", ".join(imports)
        )


def check_umbrella_files(errors: list[str]) -> None:
    for module in PUBLIC_TRACK_IMPORTS:
        relative = module.removeprefix("LeanCondensedMatter.").replace(".", "/") + ".lean"
        path = LEAN_ROOT.parent / "LeanCondensedMatter" / relative
        if not path.is_file():
            errors.append(f"missing public umbrella module: LeanCondensedMatter/{relative}")


def main() -> int:
    errors: list[str] = []
    check_root_imports(errors)
    check_umbrella_files(errors)
    return finish_audit(
        errors,
        failure_heading="Root public-umbrella audit failed:",
        success_message="Root public-umbrella audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
