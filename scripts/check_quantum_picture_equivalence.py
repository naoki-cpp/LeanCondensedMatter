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
LEAN_ROOT = ROOT / "LeanCondensedMatter"
QUANTUM = LEAN_ROOT / "QuantumTheory"
PICTURE = QUANTUM / "LinearResponse" / "PictureEquivalence.lean"
UNITARY_TRACE = LEAN_ROOT / "Analysis" / "Operator" / "TraceClass" / "Unitary.lean"
DENSITY_DIAGONAL = QUANTUM / "DensityOperator" / "Diagonal.lean"
ROOT_UMBRELLA = ROOT / "LeanCondensedMatter" / "QuantumTheory.lean"
PICTURE_MODULE = "LeanCondensedMatter.QuantumTheory.LinearResponse.PictureEquivalence"


def relative(path: Path) -> str:
    return relative_to(ROOT, path)


def main() -> int:
    errors: list[str] = []

    required_files = (PICTURE, UNITARY_TRACE, DENSITY_DIAGONAL)
    for path in required_files:
        if not path.exists():
            errors.append(f"missing picture-equivalence boundary file: {relative(path)}")

    if errors:
        return finish_audit(
            errors,
            failure_heading="QuantumTheory picture-equivalence audit failed:",
            success_message="QuantumTheory picture-equivalence audit passed.",
        )

    picture_code = strip_lean_comments(PICTURE.read_text(encoding="utf-8"))
    unitary_code = strip_lean_comments(UNITARY_TRACE.read_text(encoding="utf-8"))

    if PICTURE_MODULE not in lean_imports(ROOT_UMBRELLA):
        errors.append(
            "QuantumTheory public umbrella must expose Schrödinger-Heisenberg picture equivalence: "
            f"{relative(ROOT_UMBRELLA)}"
        )

    for path, code in ((PICTURE, picture_code), (UNITARY_TRACE, unitary_code)):
        for finite_assumption in ("[FiniteDimensional", "[Fintype"):
            if finite_assumption in code:
                errors.append(
                    "picture-equivalence foundations must remain dimension-independent; found "
                    f"`{finite_assumption}` in {relative(path)}"
                )

    return finish_audit(
        errors,
        failure_heading="QuantumTheory picture-equivalence audit failed:",
        success_message="QuantumTheory picture-equivalence audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
