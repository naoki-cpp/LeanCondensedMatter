"""Advisory inventory of long, unreferenced MassiveDirac theorem names.

Run after generating the compiled theorem catalog:
    python3 scripts/audit_long_massive_dirac_theorems.py docs/generated/theorems.json

The evidence is *only* compiled proof-consumer count; no deletion or public
rename is justified by this report without source-level/semantic review.
"""
import argparse
import csv
import json
import sys
from pathlib import Path

MODEL_MODULE_PREFIX = "LeanCondensedMatter.Models.MassiveDirac."
MODEL_NAME_PREFIX = "QuantumTheory.Models.MassiveDirac."

# Reviewed endpoints with standalone physical/mathematical meaning. These are
# provisional API dispositions, not additions to the retained-theorem registry.
PRESERVE_ENDPOINTS = {
    "QuantumTheory.Models.MassiveDirac.tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator_broadening_zero_of_boundary_realRenormalization_lt_one",
    "QuantumTheory.Models.MassiveDirac.eventually_finiteCutoffContinuumBornDysonLadderRegular_broadening_zero_of_boundary_realRenormalization_lt_one",
    "QuantumTheory.Models.MassiveDirac.finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity_psi_eq_explicit_k0_k1_k2_moments_integral",
    "QuantumTheory.Models.MassiveDirac.finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity_x_eq_explicit_k0_k1_k2_moments_integral",
    "QuantumTheory.Models.MassiveDirac.FiniteCutoffBornDyson.Longitudinal.ZeroBroadeningWeakDisorder.tendsto_disorder_mul_conductivity_born_rta",
    "QuantumTheory.Models.MassiveDirac.finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_diagonal_spectral_difference",
    "QuantumTheory.Models.MassiveDirac.orderedXYRungSolvedProvenanceConductivityLimit_eq_intrinsic_sideJumpType_nonCrossingSkewType_partition",
    "QuantumTheory.Models.MassiveDirac.finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator_eq_rotatedResummed",
    "QuantumTheory.Models.MassiveDirac.finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrent_origin_scalar_and_z_eq_zero",
    "QuantumTheory.Models.MassiveDirac.norm_averagedHallCurrentTrace_sub_meanProduct_le_uniformPotential_sq",
    "QuantumTheory.Models.MassiveDirac.ScalarImpurityParameters.matrixOperator_tMatrix_eq_ringInverse_shift",
    "QuantumTheory.Models.MassiveDirac.tendsto_finiteCutoffContinuumBornScalarIntegral_im_broadening_zero",
}

# These statements may be folded into a more canonical public bridge, but
# source-level use and proof/API significance must be checked before edits.
CONSOLIDATION_REVIEW = {
    "QuantumTheory.Models.MassiveDirac.finiteCutoffContinuumBornDysonOrderedXYRetardedAdvancedDressedSurfaceMomentumIntegralZeroBroadeningBoundary_eq_rungSolvedProvenance",
    "QuantumTheory.Models.MassiveDirac.AheBornRtaParameters.bornRtaLongitudinalConductivity_eq_coefficient_div_disorderStrength",
    "QuantumTheory.Models.MassiveDirac.finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivityTotal_eq_x_add_psi",
}

FIELDNAMES = (
    "length", "name", "module", "compiled_consumers", "triage",
    "reason", "source_url",
)


def classify(entry):
    name = entry["name"]
    if entry.get("retainedMention", False):
        return "preserve_registry", "Already retained by semantic theorem audit"
    if entry.get("simpLemma", False):
        return "preserve_simp", "Public normalization rule; compiled usage can miss simp"
    if name in PRESERVE_ENDPOINTS:
        return "preserve_endpoint", "Distinct physical endpoint or mathematical bridge"
    if name in CONSOLIDATION_REVIEW:
        return "consolidation_review", "Inspect canonical equivalent before API changes"
    return "semantic_review", "Consumer count alone cannot determine public value"


def inventory(theorems, min_length=100):
    """Return long public MassiveDirac theorems with zero compiled consumers."""
    result = []
    for entry in theorems:
        name = entry.get("name", "")
        module = entry.get("module", "")
        if not isinstance(name, str) or not isinstance(module, str):
            continue
        if name.startswith("_private."):
            continue
        if not name.startswith(MODEL_NAME_PREFIX):
            continue
        if not module.startswith(MODEL_MODULE_PREFIX):
            continue
        if len(name) < min_length or entry.get("compiledConsumerCount") != 0:
            continue
        triage, reason = classify(entry)
        source = module.replace(".", "/") + ".lean"
        result.append({
            "length": len(name),
            "name": name,
            "module": module,
            "compiled_consumers": 0,
            "triage": triage,
            "reason": reason,
            "source_url": (
                "https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/" + source
            ),
        })
    result.sort(key=lambda row: (-row["length"], row["name"]))
    return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("catalog", type=Path, help="Compiled theorems.json")
    parser.add_argument("--min-length", type=int, default=100)
    parser.add_argument("--output", type=Path, help="CSV file (stdout by default)")
    args = parser.parse_args(argv)
    if args.min_length < 0:
        parser.error("--min-length must be nonnegative")
    rows = inventory(json.loads(args.catalog.read_text(encoding="utf-8")),
                     min_length=args.min_length)
    if args.output:
        with args.output.open("w", encoding="utf-8", newline="") as stream:
            writer = csv.DictWriter(stream, fieldnames=FIELDNAMES)
            writer.writeheader()
            writer.writerows(rows)
    else:
        writer = csv.DictWriter(sys.stdout, fieldnames=FIELDNAMES)
        writer.writeheader()
        writer.writerows(rows)
    print(f"Advisory: {len(rows)} candidates; no automatic deletions.",
          file=sys.stderr)


if __name__ == "__main__":
    main()
