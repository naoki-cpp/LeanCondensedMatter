# MassiveDirac: long, zero-compiled-consumer theorem audit (advisory)

Source snapshots: `main` [`dacfcdf1d80f`](https://github.com/naoki-cpp/LeanCondensedMatter/commit/dacfcdf1d80fa4c9c8d88b0c07c657a535ba6986), `graph-data` [`07d6e5bf92e4`](https://github.com/naoki-cpp/LeanCondensedMatter/commit/07d6e5bf92e4834cf87997c81c77c63fe3604d91) (2026-11-19 UTC).
This is a **snapshot**, not an always-current deletion queue. A newer `main` or catalog requires re-running the report.

## Scope and limits

- Select project theorems whose *declaring module* starts with `LeanCondensedMatter.Models.MassiveDirac.`, whose name is in the `QuantumTheory.Models.MassiveDirac` namespace, and whose fully qualified name has **at least 100 characters**.
- Exclude Lean-generated `_private.` names; require `compiledConsumerCount = 0`. This is not proof of zero source references, zero tactic use, or zero public/API value.
- **Do not automatically remove, rename, privatize, or add to the retained registry.** [ADR 0020](../adr/0020-theorem-catalog-advisory.md) and [the retained registry](../theorem-catalog-retained.md) require semantic inspection before changes.
- Triage classifications below are provisional; `preserve_endpoint` is **not** the catalog's `retainedMention` attribute.

## Results

63 candidates. Counts:

| Triage | Count | Meaning |
| --- | ---: | --- |
| `preserve_endpoint` | 12 | Individually examined domain-level limit, conductivity, or proof boundary; keep public in this pass |
| `preserve_simp` | 8 | `@[simp]` normal form, which may be used by elaboration without an explicit proof-term edge |
| `consolidation_review` | 3 | A short algebraic/definitional bridge; examine canonical ownership before changing its API |
| `semantic_review` | 40 | Requires source-level and semantic review; zero compiled consumers alone is insufficient |

### Three first candidates to investigate (not approved deletions)

1. [`...OrderedXYRetardedAdvancedDressedSurfaceMomentumIntegralZeroBroadeningBoundary_eq_rungSolvedProvenance`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Streda/BornLadder/HallZeroBroadeningProvenance.lean). The proof reduces the canonical `inPlaneLadderAction` with `simp` and `ring`. Inspect whether this domain-level provenance boundary is an intentional exported statement or can be inlined at its eventual use.
2. [`AheBornRtaParameters.bornRtaLongitudinalConductivity_eq_coefficient_div_disorderStrength`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Scaling/Longitudinal.lean). An algebraic rearrangement of `disorderStrength_mul_bornRtaLongitudinalConductivity_eq`. Check whether one canonical orientation suffices; do not erase a convenient downstream rewrite rule without checking.
3. [`...GaussianCrossedOrderedXYConductivityTotal_eq_x_add_psi`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Conductivity/Hall/GaussianCrossed.lean). A `sum_gaussianCrossedDiagram` bridge. Investigate whether this is an intentional public reduction equation and whether it should be the canonical `@[simp]`/rewrite API.

A code search of current `main` for these three full names found only their declaration files; verify again before any code change, including documentation references and local implicit uses.

### Complete ranking (full-name lengths)

The table omits the repeated `QuantumTheory.Models.MassiveDirac.` prefix from display only; lengths include the full prefix. Names link to their defining modules.

| # | Characters | Declaration (after shared namespace prefix) | Triage |
| ---: | ---: | --- | --- |
| 1 | 171 | [`tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator_broadening_zero_of_boundary_realRenormalization_lt_one`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Disorder/FiniteBroadeningCurrentVertexResponse.lean) | `preserve_endpoint` |
| 2 | 165 | [`finiteCutoffContinuumBornDysonOrderedXYRetardedAdvancedDressedSurfaceMomentumIntegralZeroBroadeningBoundary_eq_rungSolvedProvenance`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Streda/BornLadder/HallZeroBroadeningProvenance.lean) | `consolidation_review` |
| 3 | 143 | [`eventually_finiteCutoffContinuumBornDysonLadderRegular_broadening_zero_of_boundary_realRenormalization_lt_one`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Disorder/FiniteBroadeningLadderZeroBroadening.lean) | `preserve_endpoint` |
| 4 | 142 | [`finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity_psi_eq_explicit_k0_k1_k2_moments_integral`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Conductivity/Hall/GaussianCrossed.lean) | `preserve_endpoint` |
| 5 | 140 | [`finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity_x_eq_explicit_k0_k1_k2_moments_integral`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Conductivity/Hall/GaussianCrossed.lean) | `preserve_endpoint` |
| 6 | 139 | [`finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity_x_eq_retardedGenerator_radial_integral`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Conductivity/Hall/GaussianCrossed.lean) | `semantic_review` |
| 7 | 138 | [`FiniteCutoffBornDyson.Longitudinal.ZeroBroadeningWeakDisorder.tendsto_disorder_mul_conductivity_born_rta`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Conductivity/FiniteBroadeningBornLadderLongitudinalWeakDisorder.lean) | `preserve_endpoint` |
| 8 | 137 | [`finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_diagonal_spectral_difference`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Streda/GaussianCrossed/RadialHarmonics.lean) | `preserve_endpoint` |
| 9 | 137 | [`ScalarImpurityParameters.quadraticCleanLoopSelfEnergy_eq_finiteCutoffContinuumBornSelfEnergyOfRegulator`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Disorder/TMatrix/BornDysonLoop.lean) | `semantic_review` |
| 10 | 136 | [`orderedXYRungSolvedProvenanceConductivityLimit_eq_intrinsic_sideJumpType_nonCrossingSkewType_partition`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Conductivity/Hall/NonCrossingMechanismClassification.lean) | `preserve_endpoint` |
| 11 | 134 | [`finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity_psi_eq_real_minor_radial_integral`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Conductivity/Hall/GaussianCrossed.lean) | `semantic_review` |
| 12 | 134 | [`finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity_psi_eq_transverse_radial_integral`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Conductivity/Hall/GaussianCrossed.lean) | `semantic_review` |
| 13 | 133 | [`continuumBornUpperBandTransportLifetime_eq_weakDisorderCurrentRungFactor_mul_singleParticleLifetime`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Disorder/BornCurrentVertexWeakDisorder.lean) | `semantic_review` |
| 14 | 132 | [`finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity_x_eq_transverse_radial_integral`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Conductivity/Hall/GaussianCrossed.lean) | `semantic_review` |
| 15 | 131 | [`finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_origin_diagonal_eq_log`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Streda/GaussianCrossed/RadialHarmonics.lean) | `semantic_review` |
| 16 | 127 | [`finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator_eq_rotatedResummed`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Disorder/FiniteBroadeningCurrentVertexResponse.lean) | `preserve_endpoint` |
| 17 | 127 | [`tendsto_finiteCutoffContinuumBornDysonOrderedXYRungSolvedProvenanceConductivity_disorder_zero`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Conductivity/Hall/NonCrossingMechanismClassification.lean) | `semantic_review` |
| 18 | 127 | [`tendsto_finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungCoefficient_x_disorder_zero`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Disorder/BornCurrentVertexWeakDisorder.lean) | `semantic_review` |
| 19 | 126 | [`tendsto_continuumBornRetardedAdvancedPauliXCurrentRungCoefficientUV_y_div_gamma_weakDisorder`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Disorder/BornCurrentVertexInfiniteCutoff.lean) | `semantic_review` |
| 20 | 122 | [`AheBornRtaParameters.bornRtaLongitudinalConductivity_eq_coefficient_div_disorderStrength`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Scaling/Longitudinal.lean) | `consolidation_review` |
| 21 | 120 | [`finiteCutoffContinuumBornDysonGaussianCrossedInPlaneTransverse_gap_eq_Green_difference`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Streda/GaussianCrossed/CurrentInPlaneResolvent.lean) | `semantic_review` |
| 22 | 120 | [`finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrent_origin_scalar_and_z_eq_zero`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Streda/GaussianCrossed/RadialHarmonics.lean) | `preserve_endpoint` |
| 23 | 119 | [`finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivityTotal_zero_disorder`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Conductivity/Hall/GaussianCrossed.lean) | `preserve_simp` |
| 24 | 119 | [`finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceTraceBridge_zero_disorder`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Streda/BornLadder/TraceBridge.lean) | `preserve_simp` |
| 25 | 119 | [`finiteCutoffContinuumBornDysonRetardedAdvancedLongitudinalCurrentFactor_zero_disorder`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Disorder/FiniteBroadeningCurrentVertexResponse.lean) | `preserve_simp` |
| 26 | 118 | [`finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivityTotal_eq_x_add_psi`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Conductivity/Hall/GaussianCrossed.lean) | `consolidation_review` |
| 27 | 117 | [`tendsto_finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungCoefficient_atTop`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Disorder/BornCurrentVertexInfiniteCutoff.lean) | `semantic_review` |
| 28 | 116 | [`tendsto_continuumBornRetardedAdvancedPauliXCurrentRungCoefficientUV_x_weakDisorder`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Disorder/BornCurrentVertexInfiniteCutoff.lean) | `semantic_review` |
| 29 | 116 | [`tendsto_finiteCutoffContinuumBornRetardedUpperBandFermiProjection_im_dampingEnergy`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Disorder/Born/Damping.lean) | `semantic_review` |
| 30 | 115 | [`continuumBornUpperBandSingleParticleScatteringRate_eq_prefactor_mul_angularWeight`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Disorder/TransportRate.lean) | `semantic_review` |
| 31 | 115 | [`finiteCutoffContinuumBornDenominatorIntegralOfRegulator_re_eq_log_sqrt_polynomial`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Disorder/Born/Denominator.lean) | `semantic_review` |
| 32 | 115 | [`finiteCutoffContinuumBornDysonGaussianCrossedInPlaneTrace_gap_eq_Green_difference`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Streda/GaussianCrossed/CurrentInPlaneResolvent.lean) | `semantic_review` |
| 33 | 115 | [`tendsto_finiteCutoffContinuumBornSelfEnergyCoefficient_scalar_normalized_re_atBot`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Disorder/Born/UltravioletSelfEnergy.lean) | `semantic_review` |
| 34 | 113 | [`finiteCutoffContinuumBornDysonGaussianCrossedScalarCurrent_sourceY_gap_gradient`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Streda/GaussianCrossed/CurrentGradientSourceY.lean) | `semantic_review` |
| 35 | 112 | [`finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity_x_zero_mass`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Conductivity/Hall/GaussianCrossed.lean) | `preserve_simp` |
| 36 | 110 | [`finiteCutoffContinuumBornDysonRadialGreenScalarZ_zero_disorder_tendsto_atTop`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Disorder/FiniteBroadeningBornRadialFrozenUV.lean) | `semantic_review` |
| 37 | 110 | [`tendsto_finiteCutoffContinuumBornSelfEnergyCoefficient_z_normalized_re_atBot`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Disorder/Born/UltravioletSelfEnergy.lean) | `semantic_review` |
| 38 | 109 | [`AheScalingParameters.tendsto_zeroBroadeningPairAtDisorder_sxy_disorder_zero`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Scaling/Pair.lean) | `semantic_review` |
| 39 | 109 | [`finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix_eq_scalarGenerator`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Disorder/FiniteBroadeningBornRadialScalarGenerator.lean) | `semantic_review` |
| 40 | 109 | [`finiteCutoffContinuumBornRetardedAdvancedPauliXRadialCoefficient_y_massless`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Disorder/BornCurrentVertexRung.lean) | `preserve_simp` |
| 41 | 108 | [`finiteCutoffContinuumBornDysonGaussianCrossedZCurrent_sourceY_gap_gradient`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Streda/GaussianCrossed/CurrentGradientSourceY.lean) | `semantic_review` |
| 42 | 108 | [`ScalarImpurityParameters.selfEnergy_eq_meanPotential_add_tMatrix_remainder`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Disorder/TMatrix/ScalarImpurity.lean) | `semantic_review` |
| 43 | 108 | [`tendsto_finiteCutoffContinuumBornEffectiveEnergy_shift_normalized_re_atBot`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Disorder/Born/UltravioletSelfEnergy.lean) | `semantic_review` |
| 44 | 107 | [`finiteCutoffContinuumBornDysonAngularRetardedAdvancedInPlaneRungAction_eq`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Disorder/FiniteBroadeningCurrentVertex.lean) | `semantic_review` |
| 45 | 107 | [`finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity_psi_im`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Conductivity/Hall/GaussianCrossed.lean) | `preserve_simp` |
| 46 | 106 | [`finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor_zero_disorder`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Streda/GaussianCrossed/RealSpace.lean) | `preserve_simp` |
| 47 | 106 | [`tendsto_finiteCutoffContinuumBornEffectiveMass_shift_normalized_re_atBot`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Disorder/Born/UltravioletSelfEnergy.lean) | `semantic_review` |
| 48 | 105 | [`finiteCutoffContinuumBornDysonGaussianCrossedScalarCurrent_gap_gradient`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Streda/GaussianCrossed/CurrentGradientDerivative.lean) | `semantic_review` |
| 49 | 105 | [`nonCrossingHallConductivity_sub_intrinsicHallConductivity_eq_ado_eq12bc`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Conductivity/Hall/NonCrossingDecomposition.lean) | `semantic_review` |
| 50 | 105 | [`norm_targetCenteredZeroTemperatureInterbandBastinPairIntegral_radial_le`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Bastin/ZeroTemperaturePair.lean) | `semantic_review` |
| 51 | 104 | [`finiteCutoffContinuumBornDysonGaussianCrossedTraceKernel_radialAxis_eq`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Streda/GaussianCrossed/RadialTrace.lean) | `semantic_review` |
| 52 | 104 | [`tendsto_disorderStrength_mul_bornRtaLongitudinalConductivityClosedForm`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Scaling/Longitudinal.lean) | `semantic_review` |
| 53 | 103 | [`AheScalingParameters.tendsto_finiteBroadeningPair_sxx_broadening_zero`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Scaling/Pair.lean) | `semantic_review` |
| 54 | 103 | [`AheScalingParameters.tendsto_finiteBroadeningPair_sxy_broadening_zero`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Scaling/Pair.lean) | `semantic_review` |
| 55 | 103 | [`finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel_psi_im`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Streda/GaussianCrossed/RadialTrace.lean) | `preserve_simp` |
| 56 | 103 | [`finiteCutoffContinuumBornDysonRadialGreenPauli_x_conj_eq_neg_advanced`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Disorder/FiniteBroadeningBornRadialConjugation.lean) | `semantic_review` |
| 57 | 102 | [`FiniteScalarDisorderModel.bornSelfEnergyOfRegulator_eq_strength_smul`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Disorder/ScalarCovariance.lean) | `semantic_review` |
| 58 | 102 | [`intrinsic_sideJumpType_adoEq18SkewBenchmark_sum_eq_gaussianBenchmark`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Conductivity/Hall/GaussianCrossedBenchmark.lean) | `semantic_review` |
| 59 | 102 | [`norm_averagedHallCurrentTrace_sub_meanProduct_le_uniformPotential_sq`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Streda/BornLadder/DisorderComparison.lean) | `preserve_endpoint` |
| 60 | 102 | [`ScalarImpurityParameters.matrixOperator_tMatrix_eq_ringInverse_shift`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Disorder/TMatrix/ScalarImpurity.lean) | `preserve_endpoint` |
| 61 | 100 | [`finiteCutoffContinuumBornDysonGaussianCrossedZCurrent_gap_gradient`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Streda/GaussianCrossed/CurrentGradientDerivative.lean) | `semantic_review` |
| 62 | 100 | [`finiteCutoffContinuumBornDysonRadialFrozenUVValue_eq_besselJCenter`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Disorder/Born/RadialUVBesselJ.lean) | `semantic_review` |
| 63 | 100 | [`tendsto_finiteCutoffContinuumBornScalarIntegral_im_broadening_zero`](https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/LeanCondensedMatter/Models/MassiveDirac/Disorder/Born/Damping.lean) | `preserve_endpoint` |

## Reproduce the audit

After running the repository's existing theorem-catalog generation workflow:

```bash
python3 scripts/audit_long_massive_dirac_theorems.py docs/generated/theorems.json --output massive-dirac-long-terminal.csv
python3 -m unittest discover -s scripts -p 'test_long_massive_dirac_theorem_audit.py'
```

The CSV contains the **full** names, module paths, lengths, compiled consumer counts, provisional dispositions, reasons, and links. The script reads a supplied local catalog; it does not fetch GitHub or mutate Lean sources. The snapshot's counts are expected to change as `main` evolves.

## Next refactor acceptance checks

Before acting on any `consolidation_review` item:

1. Confirm current full name, signature, proof, source references, doc references, and relevant `@[simp]` behavior.
2. Identify the canonical same-fact declaration or document why the theorem is an independent semantic/API boundary.
3. If removing or privatizing, migrate all source uses and prove no public theorem API is lost unintentionally; run `lake build --wfail` and the repository's source audit.
4. Keep changes scoped to one small cluster. Do **not** infer a broader deletion policy from name length or consumer counts.
