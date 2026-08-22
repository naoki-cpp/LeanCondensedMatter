from __future__ import annotations

from pathlib import Path

from architecture_audit_common import (
    finish_audit,
    lean_imports,
    relative as relative_to,
    repository_root,
    strip_lean_comments,
)

ROOT = repository_root(__file__)
QUANTUM = ROOT / "LeanCondensedMatter" / "QuantumTheory"
EQUATIONS = QUANTUM / "LinearResponse" / "EquationsOfMotion.lean"
ROOT_UMBRELLA = ROOT / "LeanCondensedMatter" / "QuantumTheory.lean"
EQUATIONS_MODULE = "LeanCondensedMatter.QuantumTheory.LinearResponse.EquationsOfMotion"


def relative(path: Path) -> str:
    return relative_to(ROOT, path)


def main() -> int:
    errors: list[str] = []

    if not EQUATIONS.exists():
        errors.append(f"missing bounded equations-of-motion module: {relative(EQUATIONS)}")
        return finish_audit(
            errors,
            failure_heading="QuantumTheory equations-of-motion audit failed:",
            success_message="QuantumTheory equations-of-motion audit passed.",
        )

    code = strip_lean_comments(EQUATIONS.read_text(encoding="utf-8"))

    if EQUATIONS_MODULE not in lean_imports(ROOT_UMBRELLA):
        errors.append(
            "QuantumTheory public umbrella must expose bounded equations of motion: "
            f"{relative(ROOT_UMBRELLA)}"
        )

    for finite_assumption in ("[FiniteDimensional", "[Fintype"):
        if finite_assumption in code:
            errors.append(
                "bounded equations of motion must remain dimension-independent; found "
                f"`{finite_assumption}` in {relative(EQUATIONS)}"
            )

    return finish_audit(
        errors,
        failure_heading="QuantumTheory equations-of-motion audit failed:",
        success_message="QuantumTheory equations-of-motion audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
