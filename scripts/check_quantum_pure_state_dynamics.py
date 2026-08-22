from __future__ import annotations

from pathlib import Path

from architecture_audit_common import finish_audit, lean_imports, relative as relative_to, repository_root

ROOT = repository_root(__file__)
QUANTUM = ROOT / "LeanCondensedMatter" / "QuantumTheory"
QUANTUM_UMBRELLA = ROOT / "LeanCondensedMatter" / "QuantumTheory.lean"
PURE_DYNAMICS = QUANTUM / "LinearResponse" / "PureStateDynamics.lean"
PURE_DYNAMICS_MODULE = "LeanCondensedMatter.QuantumTheory.LinearResponse.PureStateDynamics"


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

    # Dimension independence is a compiled declaration-type contract.
    if PURE_DYNAMICS_MODULE not in lean_imports(QUANTUM_UMBRELLA):
        errors.append(
            "QuantumTheory public umbrella must expose bounded pure-state dynamics: "
            f"{relative(QUANTUM_UMBRELLA)}"
        )

    return finish_audit(
        errors,
        failure_heading="QuantumTheory pure-state dynamics audit failed:",
        success_message="QuantumTheory pure-state dynamics audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
