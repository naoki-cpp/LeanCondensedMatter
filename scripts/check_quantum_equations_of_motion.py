from __future__ import annotations

import re
from pathlib import Path

from architecture_audit_common import (
    finish_audit,
    lean_files,
    relative as relative_to,
    repository_root,
    strip_lean_comments,
)

ROOT = repository_root(__file__)
QUANTUM = ROOT / "LeanCondensedMatter" / "QuantumTheory"
EQUATIONS = QUANTUM / "LinearResponse" / "EquationsOfMotion.lean"
ROOT_UMBRELLA = ROOT / "LeanCondensedMatter" / "QuantumTheory.lean"
EQUATIONS_IMPORT = (
    "import LeanCondensedMatter.QuantumTheory.LinearResponse.EquationsOfMotion"
)

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
    normalized = " ".join(code.split())
    root_code = ROOT_UMBRELLA.read_text(encoding="utf-8")

    for declaration in REQUIRED_DECLARATIONS:
        if declaration not in code:
            errors.append(
                f"missing bounded-dynamics declaration `{declaration}` in {relative(EQUATIONS)}"
            )

    if EQUATIONS_IMPORT not in root_code:
        errors.append(
            "QuantumTheory public umbrella must expose bounded equations of motion: "
            f"{relative(ROOT_UMBRELLA)}"
        )

    for name in CANONICAL_NAMES:
        owners: list[Path] = []
        pattern = declaration_pattern(name)
        for path in lean_files(QUANTUM):
            path_code = strip_lean_comments(path.read_text(encoding="utf-8"))
            if pattern.search(path_code):
                owners.append(path)
        if owners != [EQUATIONS]:
            rendered = ", ".join(relative(path) for path in owners) or "<none>"
            errors.append(
                f"canonical declaration `{name}` must be owned exactly once by "
                f"{relative(EQUATIONS)}; found: {rendered}"
            )

    required_boundaries = (
        "hasDerivAt_exp_smul_const'",
        "hasDerivAt_iff_tendsto",
        "schrodingerGenerator system",
        "Complex.I / (system.hbar : ℂ)",
        "(-(Complex.I / (system.hbar : ℂ)))",
        "heisenbergEvolution system A",
        "evolveDensityOperator system ρ",
    )
    for boundary in required_boundaries:
        if boundary not in normalized:
            errors.append(
                f"bounded equations must retain `{boundary}` in {relative(EQUATIONS)}"
            )

    for finite_assumption in ("[FiniteDimensional", "[Fintype"):
        if finite_assumption in code:
            errors.append(
                "bounded equations of motion must remain dimension-independent; found "
                f"`{finite_assumption}` in {relative(EQUATIONS)}"
            )

    if "Differentiable" in code and "HasDerivAt" not in code:
        errors.append(
            "equations of motion must expose the actual norm derivatives, not only generic "
            f"differentiability, in {relative(EQUATIONS)}"
        )

    return finish_audit(
        errors,
        failure_heading="QuantumTheory equations-of-motion audit failed:",
        success_message="QuantumTheory equations-of-motion audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
