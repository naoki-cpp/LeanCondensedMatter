import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Hall.NonCrossingDecomposition
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderHallZeroBroadeningProvenance
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Mechanism classification of the massive-Dirac non-crossing Hall result

This module connects the concrete ordered-`xy` ladder provenance isolated upstream to the Ado et al.
EPL 111, 37004 (2015), Eq. (12a-c) non-crossing decomposition. Mechanism names remain theorem-level:
no primitive side-jump or skew-scattering conductivity definitions are introduced.

After physical conductivity normalization, the two concrete weak-disorder provenance terms do not
map one-to-one to mechanisms. Instead, with `P₀` the `r_y Γ_x` contribution and `P₁` the
`r_x Γ_y` contribution,

```text
P₀ = intrinsic + 3/4 · side-jump-type,
P₁ = 1/4 · side-jump-type + Gaussian-skew-type.
```

Thus the side-jump-type contribution is distributed across both ladder provenance terms. This
classification uses the repository `Gᴿ Γ Gᴬ` orientation already fixed by the upstream Středa chain.
Crossed `X/Ψ` diagrams and non-Gaussian `C3` skew scattering remain outside this module.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter QuantumTheory.Transport

/-- Physical conductivity normalization of the two concrete ordered-`xy` rung/solved provenance
terms. Component `0` remains the `r_y Γ_x` contribution and component `1` remains the
`r_x Γ_y` contribution. -/
theorem tendsto_finiteCutoffContinuumBornDysonOrderedXYRungSolvedProvenanceConductivity_disorder_zero
    (e v m probeEnergy hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hhbar : 0 < hbar)
    (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun disorderStrength : ℝ =>
        let q : ℂ := (((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))
        let pref : ℂ := ((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ)
        let solved := finiteCutoffContinuumBornDysonLadderSolvedVectorZeroBroadeningBoundary
          v m probeEnergy disorderStrength hbar pMax
        let rung := finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary
          v m probeEnergy disorderStrength hbar pMax
        let normalization : ℂ := ((bastinStredaConductivityNormalization hbar : ℝ) : ℂ)
        inPlaneCoefficientVector
          (normalization * ((-2 : ℂ) * q ^ 2 * pref⁻¹ * (rung 1 * solved 0)))
          (normalization * ((-2 : ℂ) * q ^ 2 * pref⁻¹ * (rung 0 * solved 1))))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (inPlaneCoefficientVector
          (((-e ^ 2 * probeEnergy * m /
            (Real.pi * hbar * (probeEnergy ^ 2 + 3 * m ^ 2)) : ℝ) : ℂ))
          (((-e ^ 2 * probeEnergy * m * (probeEnergy ^ 2 - m ^ 2) /
            (Real.pi * hbar * (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2) : ℝ) : ℂ)))) := by
  have hhbarNe : hbar ≠ 0 := ne_of_gt hhbar
  have hraw :=
    tendsto_finiteCutoffContinuumBornDysonOrderedXYRungSolvedProvenance_disorder_zero
      e v m probeEnergy hbar pMax hvelocity hhbarNe hmetal hcutoff
  have h0 :
      Tendsto
        (fun disorderStrength : ℝ =>
          let q : ℂ := (((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))
          let pref : ℂ := ((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ)
          let solved := finiteCutoffContinuumBornDysonLadderSolvedVectorZeroBroadeningBoundary
            v m probeEnergy disorderStrength hbar pMax
          let rung := finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary
            v m probeEnergy disorderStrength hbar pMax
          (-2 : ℂ) * q ^ 2 * pref⁻¹ * (rung 1 * solved 0))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (((-8 * Real.pi ^ 2 * e ^ 2 * probeEnergy * m /
            (probeEnergy ^ 2 + 3 * m ^ 2) : ℝ) : ℂ))) := by
    simpa [inPlaneCoefficientVector] using tendsto_pi_nhds.mp hraw (0 : Fin 2)
  have h1 :
      Tendsto
        (fun disorderStrength : ℝ =>
          let q : ℂ := (((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))
          let pref : ℂ := ((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ)
          let solved := finiteCutoffContinuumBornDysonLadderSolvedVectorZeroBroadeningBoundary
            v m probeEnergy disorderStrength hbar pMax
          let rung := finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary
            v m probeEnergy disorderStrength hbar pMax
          (-2 : ℂ) * q ^ 2 * pref⁻¹ * (rung 0 * solved 1))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (((-8 * Real.pi ^ 2 * e ^ 2 * probeEnergy * m *
            (probeEnergy ^ 2 - m ^ 2) /
            (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2 : ℝ) : ℂ))) := by
    simpa [inPlaneCoefficientVector] using tendsto_pi_nhds.mp hraw (1 : Fin 2)
  let normalization : ℂ := ((bastinStredaConductivityNormalization hbar : ℝ) : ℂ)
  have hprobe : 0 < probeEnergy := lt_of_le_of_lt (abs_nonneg m) hmetal
  have hden : probeEnergy ^ 2 + 3 * m ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero (ne_of_gt hprobe), sq_nonneg m]
  have htarget0 :
      normalization *
          (((-8 * Real.pi ^ 2 * e ^ 2 * probeEnergy * m /
            (probeEnergy ^ 2 + 3 * m ^ 2) : ℝ) : ℂ)) =
        (((-e ^ 2 * probeEnergy * m /
          (Real.pi * hbar * (probeEnergy ^ 2 + 3 * m ^ 2)) : ℝ) : ℂ)) := by
    dsimp [normalization]
    unfold bastinStredaConductivityNormalization bastinTraceConductivityPrefactor
      momentumMeasurePrefactor
    push_cast
    field_simp [hhbarNe, hden, Real.pi_ne_zero]
    ring
  have htarget1 :
      normalization *
          (((-8 * Real.pi ^ 2 * e ^ 2 * probeEnergy * m *
            (probeEnergy ^ 2 - m ^ 2) /
            (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2 : ℝ) : ℂ)) =
        (((-e ^ 2 * probeEnergy * m * (probeEnergy ^ 2 - m ^ 2) /
          (Real.pi * hbar * (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2) : ℝ) : ℂ)) := by
    dsimp [normalization]
    unfold bastinStredaConductivityNormalization bastinTraceConductivityPrefactor
      momentumMeasurePrefactor
    push_cast
    field_simp [hhbarNe, hden, Real.pi_ne_zero]
    ring
  have h0Normalized := h0.const_mul normalization
  have h1Normalized := h1.const_mul normalization
  rw [htarget0] at h0Normalized
  rw [htarget1] at h1Normalized
  apply tendsto_pi_nhds.mpr
  intro i
  fin_cases i
  · simpa [inPlaneCoefficientVector, normalization] using h0Normalized
  · simpa [inPlaneCoefficientVector, normalization] using h1Normalized

/-- The physically normalized concrete provenance vector partitions the Ado Eq. (12) mechanisms.
The side-jump-type term is shared between the two provenance components rather than attached to only
one of them. The `sideJumpType` and `gaussianSkewType` names are local to this theorem statement and
do not create primitive mechanism APIs. -/
theorem orderedXYRungSolvedProvenanceConductivityLimit_eq_intrinsic_sideJumpType_gaussianSkewType_partition
    (e hbar m probeEnergy : ℝ) (hhbar : hbar ≠ 0) (hprobe : probeEnergy ≠ 0) :
    let sideJumpType : ℝ :=
      -(e ^ 2 / planckFromReduced hbar) *
        (2 * m * (probeEnergy ^ 2 - m ^ 2) /
          (probeEnergy * (probeEnergy ^ 2 + 3 * m ^ 2)))
    let gaussianSkewType : ℝ :=
      -(e ^ 2 / planckFromReduced hbar) *
        (3 * m * (probeEnergy ^ 2 - m ^ 2) ^ 2 /
          (2 * probeEnergy * (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2))
    inPlaneCoefficientVector
        (((-e ^ 2 * probeEnergy * m /
          (Real.pi * hbar * (probeEnergy ^ 2 + 3 * m ^ 2)) : ℝ) : ℂ))
        (((-e ^ 2 * probeEnergy * m * (probeEnergy ^ 2 - m ^ 2) /
          (Real.pi * hbar * (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2) : ℝ) : ℂ)) =
      inPlaneCoefficientVector
        (((intrinsicHallConductivity e hbar m probeEnergy +
          (3 / 4 : ℝ) * sideJumpType : ℝ) : ℂ))
        ((((1 / 4 : ℝ) * sideJumpType + gaussianSkewType : ℝ) : ℂ)) := by
  dsimp
  have hprobeSq : 0 < probeEnergy ^ 2 := sq_pos_of_ne_zero hprobe
  have hden : probeEnergy ^ 2 + 3 * m ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg m]
  have hx :
      -e ^ 2 * probeEnergy * m /
          (Real.pi * hbar * (probeEnergy ^ 2 + 3 * m ^ 2)) =
        intrinsicHallConductivity e hbar m probeEnergy +
          (3 / 4 : ℝ) *
            (-(e ^ 2 / planckFromReduced hbar) *
              (2 * m * (probeEnergy ^ 2 - m ^ 2) /
                (probeEnergy * (probeEnergy ^ 2 + 3 * m ^ 2)))) := by
    rw [intrinsicHallConductivity_eq_ado_eq12a e hbar m probeEnergy hhbar hprobe]
    unfold planckFromReduced
    field_simp [hhbar, hprobe, hden, Real.pi_ne_zero]
    ring
  have hy :
      -e ^ 2 * probeEnergy * m * (probeEnergy ^ 2 - m ^ 2) /
          (Real.pi * hbar * (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2) =
        (1 / 4 : ℝ) *
            (-(e ^ 2 / planckFromReduced hbar) *
              (2 * m * (probeEnergy ^ 2 - m ^ 2) /
                (probeEnergy * (probeEnergy ^ 2 + 3 * m ^ 2)))) +
          (-(e ^ 2 / planckFromReduced hbar) *
            (3 * m * (probeEnergy ^ 2 - m ^ 2) ^ 2 /
              (2 * probeEnergy * (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2))) := by
    unfold planckFromReduced
    field_simp [hhbar, hprobe, hden, Real.pi_ne_zero]
    ring
  apply funext
  intro i
  fin_cases i
  · simpa [inPlaneCoefficientVector] using congrArg Complex.ofReal hx
  · simpa [inPlaneCoefficientVector] using congrArg Complex.ofReal hy

/-- The theorem-level intrinsic, side-jump-type, and Gaussian-skew-type pieces sum to the completed
non-crossing Hall conductivity. -/
theorem intrinsic_sideJumpType_gaussianSkewType_sum_eq_nonCrossingHallConductivity
    (e hbar m probeEnergy : ℝ) (hhbar : hbar ≠ 0) (hprobe : probeEnergy ≠ 0) :
    let sideJumpType : ℝ :=
      -(e ^ 2 / planckFromReduced hbar) *
        (2 * m * (probeEnergy ^ 2 - m ^ 2) /
          (probeEnergy * (probeEnergy ^ 2 + 3 * m ^ 2)))
    let gaussianSkewType : ℝ :=
      -(e ^ 2 / planckFromReduced hbar) *
        (3 * m * (probeEnergy ^ 2 - m ^ 2) ^ 2 /
          (2 * probeEnergy * (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2))
    intrinsicHallConductivity e hbar m probeEnergy + sideJumpType + gaussianSkewType =
      nonCrossingHallConductivity e hbar m probeEnergy := by
  dsimp
  rw [nonCrossingHallConductivity_eq_ado_eq12_sum e hbar m probeEnergy hhbar hprobe]

end

end QuantumTheory.Transport.Models.MassiveDirac
