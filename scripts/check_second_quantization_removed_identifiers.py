from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN_ROOT = ROOT / "LeanCondensedMatter"

REMOVED_PATHS = {
    LEAN_ROOT
    / "SecondQuantization"
    / "Common"
    / "Thermal"
    / "NormalizedOperatorFunctional.lean":
        "removed normalized algebraic-Fock functional module",
    LEAN_ROOT
    / "SecondQuantization"
    / "Fermionic"
    / "Diagrammatics"
    / "DysonDensityStateExpansion.lean": "removed Dyson density-state forwarding module",
    LEAN_ROOT
    / "SecondQuantization"
    / "Fermionic"
    / "Thermal"
    / "FreeBoltzmannWeight.lean": "removed free Gibbs coordinate compatibility module",
}

CANONICAL_FREE_GIBBS_PATH = (
    LEAN_ROOT
    / "SecondQuantization"
    / "Fermionic"
    / "Thermal"
    / "FreeGibbsDensityOperator.lean"
)

FORBIDDEN_CANONICAL_FREE_GIBBS_TEXT = {
    "import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeBoltzmannWeight":
        "canonical free Gibbs state imports the coordinate compatibility layer",
    "freeGibbsExpectation":
        "canonical free Gibbs state mentions the coordinate expectation API",
}

DYSON_PARTITION_SERIES_PATH = (
    LEAN_ROOT
    / "SecondQuantization"
    / "Fermionic"
    / "Perturbation"
    / "DysonPartitionSeries.lean"
)
DYSON_VERTEX_MOMENT_PATH = (
    LEAN_ROOT
    / "SecondQuantization"
    / "Fermionic"
    / "Perturbation"
    / "DysonVertexMoment.lean"
)
DYSON_CORE_PATH = (
    LEAN_ROOT
    / "SecondQuantization"
    / "Fermionic"
    / "Diagrammatics"
    / "DysonDiagramExpansion"
    / "Core.lean"
)
DYSON_PAIRING_PATH = (
    LEAN_ROOT
    / "SecondQuantization"
    / "Fermionic"
    / "Diagrammatics"
    / "DysonDiagramExpansion"
    / "Pairing.lean"
)
WICK_AMPLITUDE_PATH = (
    LEAN_ROOT
    / "SecondQuantization"
    / "Fermionic"
    / "Diagrammatics"
    / "WickDiagram"
    / "Amplitude.lean"
)

FREE_BOLTZMANN_COMPATIBILITY_IMPORT = (
    "import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeBoltzmannWeight"
)

FORBIDDEN_MIGRATED_COMPATIBILITY_TEXT = {
    DYSON_PARTITION_SERIES_PATH: {
        FREE_BOLTZMANN_COMPATIBILITY_IMPORT:
            "Dyson partition series imports the coordinate compatibility layer",
    },
    DYSON_VERTEX_MOMENT_PATH: {
        FREE_BOLTZMANN_COMPATIBILITY_IMPORT:
            "Dyson vertex moments import the coordinate compatibility layer",
        "freeGibbsExpectation":
            "Dyson vertex moments mention the coordinate expectation API",
    },
    DYSON_CORE_PATH: {
        FREE_BOLTZMANN_COMPATIBILITY_IMPORT:
            "Dyson core imports the coordinate compatibility layer",
        "freeGibbsExpectation":
            "Dyson core mentions the coordinate expectation API",
    },
    DYSON_PAIRING_PATH: {
        FREE_BOLTZMANN_COMPATIBILITY_IMPORT:
            "Dyson pairing imports the coordinate compatibility layer",
        "freeGibbsExpectation":
            "Dyson pairing mentions the coordinate expectation API",
    },
    WICK_AMPLITUDE_PATH: {
        FREE_BOLTZMANN_COMPATIBILITY_IMPORT:
            "Wick amplitudes import the coordinate compatibility layer",
        "freeGibbsExpectation":
            "Wick amplitudes mention the coordinate expectation API",
    },
}

REMOVED_IDENTIFIERS = {
    re.compile(r"(?<![A-Za-z0-9_'])NormalizedOperatorFunctional(?![A-Za-z0-9_'])"):
        "removed normalized algebraic-Fock functional type",
    re.compile(r"(?<![A-Za-z0-9_'])normalizedWeightedDiagonalFunctional(?![A-Za-z0-9_'])"):
        "removed normalized weighted diagonal functional wrapper",
    re.compile(r"(?<![A-Za-z0-9_'])normalizedWeightedDiagonalLinearMap(?![A-Za-z0-9_'])"):
        "removed normalized weighted diagonal linear-map wrapper",
    re.compile(r"(?<![A-Za-z0-9_'])weightedTrace_operatorIntervalIntegral(?![A-Za-z0-9_'])"):
        "removed weighted-trace operator-integral bridge",
    re.compile(
        r"(?<![A-Za-z0-9_'])normalizedWeightedDiagonal_operatorIntervalIntegral"
        r"(?![A-Za-z0-9_'])"
    ): "removed normalized weighted-diagonal operator-integral bridge",
    re.compile(
        r"^\s*import\s+LeanCondensedMatter\.SecondQuantization\.Fermionic\.Thermal\."
        r"FreeBoltzmannWeight\s*$"
    ): "removed free Gibbs coordinate compatibility import",
    re.compile(r"(?<![A-Za-z0-9_'])freeGibbsExpectation(?![A-Za-z0-9_'])"):
        "removed free Gibbs coordinate expectation",
    re.compile(r"(?<![A-Za-z0-9_'])QuarticWickDiagram\.ext(?![A-Za-z0-9_'])"):
        "removed Fermionic WickDiagram ext wrapper",
    re.compile(r"(?<![A-Za-z0-9_'])QuarticWickDiagram\.equivPair(?![A-Za-z0-9_'])"):
        "removed Fermionic WickDiagram equivPair wrapper",
    re.compile(r"(?<![A-Za-z0-9_'])OrderedQuarticWickData(?![A-Za-z0-9_'])"):
        "removed Fermionic ordered-data alias",
    re.compile(r"(?<![A-Za-z0-9_'])quarticWickDiagramEquivOrderedData(?![A-Za-z0-9_'])"):
        "removed Fermionic ordered-data equivalence alias",
    re.compile(r"(?<![A-Za-z0-9_'])sum_quarticWickDiagram_eq_sum_orderedData(?![A-Za-z0-9_'])"):
        "removed Fermionic ordered-data sum theorem",
    re.compile(r"(?<![A-Za-z0-9_'])gibbsExpectation(?![A-Za-z0-9_'])"):
        "removed Common Gibbs expectation alias",
    re.compile(r"(?<![A-Za-z0-9_'])gibbsExpectationLinearMap(?![A-Za-z0-9_'])"):
        "removed Common Gibbs expectation linear-map wrapper",
    re.compile(
        r"(?<![A-Za-z0-9_'])gibbsExpectation_(?:"
        r"eq_normalizedWeightedDiagonal|id|add|smul|zero|list_sum|"
        r"comp_eq_div_of_zetaCommutator|comp_eq_div_of_exchangeCommutator|"
        r"comp_comp_comp_eq_div_of_zetaCommutator|four_point|peel|"
        r"peelSum_eq_sum|peel_indexed|prodComp_eq_sum_pairing"
        r")(?![A-Za-z0-9_'])"
    ): "removed Common Gibbs expectation theorem wrapper",
    re.compile(
        r"(?<![A-Za-z0-9_'])freeGibbsExpectation_(?:"
        r"numberOperator|annihilate_comp_create_self|"
        r"create_comp_annihilate|annihilate_comp_create"
        r")(?![A-Za-z0-9_'])"
    ): "removed Fermionic free Gibbs expectation theorem",
    re.compile(
        r"(?<![A-Za-z0-9_'])(?:"
        r"normalizedDysonPartitionCoeff_eq_freeGibbsExpectation|"
        r"dysonVertexMoment_eq_freeGibbsExpectation|"
        r"continuous_freeGibbsExpectation_comp_nestedVertexOperatorComp|"
        r"freeGibbsExpectation_comp_dysonCoeff_quarticInteraction|"
        r"freeGibbsExpectation_nestedVertexOperatorComp_eq_sum_pairing|"
        r"freeGibbsExpectation_quarticLegOperatorForSequence_pair_eq|"
        r"continuous_freeGibbsExpectation_quarticLegOperatorForSequence_pair|"
        r"orderedSimplexIntegral_freeGibbsExpectation_nestedVertexOperatorComp_eq_sum_pairing|"
        r"dysonVertexMoment_quarticInteraction_eq_sum_vertexLabel_pairing_densityState|"
        r"DysonDensityStateExpansion"
        r")(?![A-Za-z0-9_'])"
    ): "removed Fermionic coordinate-facing Dyson expectation API",
}


def relative(path: Path) -> str:
    return str(path.relative_to(ROOT))


def main() -> int:
    errors: list[str] = []

    for path, description in REMOVED_PATHS.items():
        if path.exists():
            errors.append(f"{description}: {relative(path)}")

    canonical_text = CANONICAL_FREE_GIBBS_PATH.read_text(encoding="utf-8")
    for forbidden, description in FORBIDDEN_CANONICAL_FREE_GIBBS_TEXT.items():
        if forbidden in canonical_text:
            errors.append(
                f"{description}: {relative(CANONICAL_FREE_GIBBS_PATH)}: {forbidden}"
            )

    for path, forbidden_text in FORBIDDEN_MIGRATED_COMPATIBILITY_TEXT.items():
        text = path.read_text(encoding="utf-8")
        for forbidden, description in forbidden_text.items():
            if forbidden in text:
                errors.append(f"{description}: {relative(path)}: {forbidden}")

    for path in sorted(LEAN_ROOT.rglob("*.lean")):
        for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            for pattern, description in REMOVED_IDENTIFIERS.items():
                if pattern.search(line):
                    errors.append(
                        f"{description}: {relative(path)}:{line_no}: {line.strip()}"
                    )

    if errors:
        print("Removed SecondQuantization identifier check failed:", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print("Removed SecondQuantization identifier check passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
