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
QUANTUM_UMBRELLA = ROOT / "LeanCondensedMatter" / "QuantumTheory.lean"
PURE_DYNAMICS = QUANTUM / "LinearResponse" / "PureStateDynamics.lean"
PURE_DYNAMICS_MODULE = "LeanCondensedMatter.QuantumTheory.LinearResponse.PureStateDynamics"
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

    if PURE_DYNAMICS_MODULE not in lean_imports(QUANTUM_UMBRELLA):
        errors.append(
            "QuantumTheory public umbrella must expose bounded pure-state dynamics: "
            f"{relative(QUANTUM_UMBRELLA)}"
        )

    evolve_declarations = lean_files_matching(QUANTUM, EVOLVE_STATE_DECL)
    if evolve_declarations != [PURE_DYNAMICS]:
        rendered = ", ".join(relative(path) for path in evolve_declarations) or "<none>"
        errors.append(
            "canonical pure-state evolution must be declared exactly once in "
            f"{relative(PURE_DYNAMICS)}; found: {rendered}"
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
