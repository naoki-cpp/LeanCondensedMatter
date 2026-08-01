from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SQ = ROOT / "LeanCondensedMatter" / "SecondQuantization"
FERMIONIC = SQ / "Fermionic"
OLD_MODULE = FERMIONIC / "Perturbation" / "ContinuousDyson.lean"
ANALYTIC_PARTITION = FERMIONIC / "Perturbation" / "AnalyticDysonPartitionFunction.lean"
UMBRELLA = FERMIONIC / "Perturbation.lean"
ARCH_CHECK = ROOT / "scripts" / "check_second_quantization_architecture.py"

OLD_IMPORT = (
    "import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.ContinuousDyson"
)


def remove_exact_import(path: Path) -> None:
    original = path.read_text(encoding="utf-8")
    lines = original.splitlines(keepends=True)
    kept = [line for line in lines if line.rstrip("\n") != OLD_IMPORT]
    if len(kept) == len(lines):
        raise RuntimeError(f"expected import not found in {path.relative_to(ROOT)}")
    path.write_text("".join(kept), encoding="utf-8")


def rewrite_analytic_partition() -> None:
    remove_exact_import(ANALYTIC_PARTITION)
    original = ANALYTIC_PARTITION.read_text(encoding="utf-8")
    updated = original

    replacements = {
        "continuousInteractingHamiltonian ε V lam":
            "Common.continuousInteractingHamiltonian (fermionEnergy ε) V lam",
        "continuousImaginaryTimeEvolveFree ε (-β)":
            "Common.continuousDiagonalEvolution (fermionEnergy ε) (-β)",
        "analyticDysonEvolution ε V β lam":
            "Common.analyticDysonEvolution (fermionEnergy ε) V β lam",
        "continuousImaginaryTimeEvolveFree_neg_mul_analyticDysonEvolution_eq_exp\n    ε V hβ lam":
            "Common.continuousDiagonalEvolution_neg_mul_analyticDysonEvolution_eq_exp\n"
            "    (fermionEnergy ε) V hβ lam",
    }
    for old, new in replacements.items():
        if old not in updated:
            raise RuntimeError(f"expected analytic-partition expression not found: {old!r}")
        updated = updated.replace(old, new)

    ANALYTIC_PARTITION.write_text(updated, encoding="utf-8")


def update_architecture_guard() -> None:
    original = ARCH_CHECK.read_text(encoding="utf-8")
    updated = original

    old_tuple = '''    SQ / "Fermionic" / "Perturbation" / "DysonExpansion.lean",
)'''
    new_tuple = '''    SQ / "Fermionic" / "Perturbation" / "DysonExpansion.lean",
    SQ / "Fermionic" / "Perturbation" / "ContinuousDyson.lean",
)'''
    if old_tuple not in updated:
        raise RuntimeError("architecture guard removed-file tuple changed")
    updated = updated.replace(old_tuple, new_tuple, 1)

    old_check = '''            if line.strip() == "import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonExpansion":
                errors.append(
                    f"removed fermionic Dyson import: {relative(path)}:{line_no}: {line.strip()}"
                )'''
    new_check = '''            if line.strip() == "import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonExpansion":
                errors.append(
                    f"removed fermionic Dyson import: {relative(path)}:{line_no}: {line.strip()}"
                )
            if line.strip() == "import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.ContinuousDyson":
                errors.append(
                    f"removed fermionic continuous-Dyson import: {relative(path)}:{line_no}: {line.strip()}"
                )'''
    if old_check not in updated:
        raise RuntimeError("architecture guard removed-import check changed")
    updated = updated.replace(old_check, new_check, 1)

    ARCH_CHECK.write_text(updated, encoding="utf-8")


def validate() -> None:
    if OLD_MODULE.exists():
        raise RuntimeError(f"obsolete module remains: {OLD_MODULE.relative_to(ROOT)}")

    errors: list[str] = []
    for path in sorted(FERMIONIC.rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        if any(line == OLD_IMPORT for line in text.splitlines()):
            errors.append(f"old import: {path.relative_to(ROOT)}")

    analytic = ANALYTIC_PARTITION.read_text(encoding="utf-8")
    obsolete_expressions = (
        "continuousInteractingHamiltonian ε V lam",
        "continuousImaginaryTimeEvolveFree ε",
        "analyticDysonEvolution ε V",
        "continuousImaginaryTimeEvolveFree_neg_mul_analyticDysonEvolution_eq_exp",
    )
    for expression in obsolete_expressions:
        if expression in analytic:
            errors.append(f"old fermionic continuous-Dyson expression: {expression}")

    if errors:
        raise RuntimeError("continuous Dyson migration incomplete:\n" + "\n".join(errors))


def main() -> None:
    if not OLD_MODULE.is_file():
        raise RuntimeError(f"missing migration source: {OLD_MODULE.relative_to(ROOT)}")
    rewrite_analytic_partition()
    remove_exact_import(UMBRELLA)
    OLD_MODULE.unlink()
    update_architecture_guard()
    validate()


if __name__ == "__main__":
    main()
