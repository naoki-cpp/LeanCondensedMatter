from __future__ import annotations

from architecture_audit_common import finish_audit, lean_imports, repository_root

ROOT = repository_root(__file__)
QUANTUM = ROOT / "LeanCondensedMatter" / "QuantumTheory"
DENSITY_UMBRELLA = QUANTUM / "DensityOperator.lean"
COUNTABLE_BRIDGE_IMPORT = "LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalExpectation"
COUNTABLE_FORMULA_IMPORT = "LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalFormula"


def main() -> int:
    errors: list[str] = []

    # Born losslessness and countable dimension independence are compiled typed contracts.
    umbrella_imports = lean_imports(DENSITY_UMBRELLA)
    if COUNTABLE_BRIDGE_IMPORT not in umbrella_imports:
        errors.append("density-state umbrella must import the Hilbert-Schmidt diagonal bridge")
    if COUNTABLE_FORMULA_IMPORT not in umbrella_imports:
        errors.append("density-state umbrella must import the countable diagonal formulas")

    return finish_audit(
        errors,
        failure_heading="QuantumTheory architecture audit failed:",
        success_message="QuantumTheory architecture audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
