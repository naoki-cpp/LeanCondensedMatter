from __future__ import annotations

import re
from pathlib import Path

from architecture_audit_common import (
    finish_audit,
    lean_files_matching,
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

REQUIRED_DECLARATIONS = (
    "theorem hasDerivAt_freePropagator",
    "theorem hasDerivAt_freePropagator_neg",
    "theorem schrodingerGenerator_commute_freePropagator",
    "theorem schrodingerEquation",
    "theorem heisenbergEquation",
    "theorem vonNeumannEquation",
)

CANONICAL_NAMES = tuple(declaration.split()[-1] for declaration in REQUIRED_DECLARATIONS)


def relative(path: Path) -> str:
    return relative_to(ROOT, path)


def declaration_pattern(name: str) -> re.Pattern[str]:
    return re.compile(
        rf"^\s*(?:noncomputable\s+)?(?:theorem|lemma|def)\s+{re.escape(name)}\b",
        re.MULTILINE,
    )


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

    for declaration in REQUIRED_DECLARATIONS:
        if declaration not in code:
            errors.append(
                f"missing bounded-dynamics declaration `{declaration}` in {relative(EQUATIONS)}"
            )

    if EQUATIONS_MODULE not in lean_imports(ROOT_UMBRELLA):
        errors.append(
            "QuantumTheory public umbrella must expose bounded equations of motion: "
            f"{relative(ROOT_UMBRELLA)}"
        )

    for name in CANONICAL_NAMES:
        owners = lean_files_matching(QUANTUM, declaration_pattern(name))
        if owners != [EQUATIONS]:
            rendered = ", ".join(relative(path) for path in owners) or "<none>"
            errors.append(
                f"canonical declaration `{name}` must be owned exactly once by "
                f"{relative(EQUATIONS)}; found: {rendered}"
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
