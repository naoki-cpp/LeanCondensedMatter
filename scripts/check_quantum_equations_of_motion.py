from __future__ import annotations

from pathlib import Path

from architecture_audit_common import finish_audit, lean_imports, relative as relative_to, repository_root

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

    # Dimension independence is checked from compiled declaration types.
    if EQUATIONS_MODULE not in lean_imports(ROOT_UMBRELLA):
        errors.append(
            "QuantumTheory public umbrella must expose bounded equations of motion: "
            f"{relative(ROOT_UMBRELLA)}"
        )

    return finish_audit(
        errors,
        failure_heading="QuantumTheory equations-of-motion audit failed:",
        success_message="QuantumTheory equations-of-motion audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
