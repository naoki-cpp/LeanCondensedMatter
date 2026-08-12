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
QUANTUM_UMBRELLA = ROOT / "LeanCondensedMatter" / "QuantumTheory.lean"
PURE_DYNAMICS = QUANTUM / "LinearResponse" / "PureStateDynamics.lean"
PURE_DYNAMICS_IMPORT = (
    "import LeanCondensedMatter.QuantumTheory.LinearResponse.PureStateDynamics"
)
EVOLVE_STATE_DECL = re.compile(
    r"^\s*noncomputable\s+def\s+evolveState\b", re.MULTILINE
)


def relative(path: Path) -> str:
    return relative_to(ROOT, path)


def main() -> int:
    errors: list[str] = []

    if not PURE_DYNAMICS.exists():
        errors.append(f"missing bounded pure-state dynamics module: {relative(PURE_DYNAMICS)}")
        return finish_audit(
            errors,
            failure_heading="QuantumTheory pure-state dynamics audit failed:",
            success_message="QuantumTheory pure-state dynamics audit passed.",
        )

    code = strip_lean_comments(PURE_DYNAMICS.read_text(encoding="utf-8"))
    normalized = " ".join(code.split())
    umbrella_code = QUANTUM_UMBRELLA.read_text(encoding="utf-8")

    required_declarations = (
        "theorem norm_freePropagator_apply",
        "def phaseState",
        "noncomputable def evolveState",
        "theorem evolveState_zero",
        "theorem evolveState_add",
        "theorem evolveState_neg_after",
        "theorem evolveState_after_neg",
        "theorem evolveState_phaseState",
    )
    for declaration in required_declarations:
        if declaration not in code:
            errors.append(
                f"missing bounded pure-state declaration `{declaration}` in "
                f"{relative(PURE_DYNAMICS)}"
            )

    if PURE_DYNAMICS_IMPORT not in umbrella_code:
        errors.append(
            "QuantumTheory public umbrella must expose bounded pure-state dynamics: "
            f"{relative(QUANTUM_UMBRELLA)}"
        )

    evolve_declarations: list[Path] = []
    for path in lean_files(QUANTUM):
        path_code = strip_lean_comments(path.read_text(encoding="utf-8"))
        if EVOLVE_STATE_DECL.search(path_code):
            evolve_declarations.append(path)
    if evolve_declarations != [PURE_DYNAMICS]:
        rendered = ", ".join(relative(path) for path in evolve_declarations) or "<none>"
        errors.append(
            "canonical pure-state evolution must be declared exactly once in "
            f"{relative(PURE_DYNAMICS)}; found: {rendered}"
        )

    if "⟨freePropagator system t ψ.1" not in normalized:
        errors.append(
            "evolveState must remain the direct normalized action of freePropagator in "
            f"{relative(PURE_DYNAMICS)}"
        )

    forbidden_projective_api = ("Quotient", "Setoid", "PureRay", "ProjectiveHilbert")
    for token in forbidden_projective_api:
        if token in code:
            errors.append(
                f"bounded pure-state dynamics must keep vector representatives rather than "
                f"introducing `{token}` in {relative(PURE_DYNAMICS)}"
            )

    for finite_assumption in ("[FiniteDimensional", "[Fintype"):
        if finite_assumption in code:
            errors.append(
                "bounded pure-state dynamics must remain dimension-independent; found "
                f"`{finite_assumption}` in {relative(PURE_DYNAMICS)}"
            )

    return finish_audit(
        errors,
        failure_heading="QuantumTheory pure-state dynamics audit failed:",
        success_message="QuantumTheory pure-state dynamics audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
