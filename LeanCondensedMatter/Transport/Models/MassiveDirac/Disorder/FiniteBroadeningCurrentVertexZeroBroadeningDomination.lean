import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertexZeroBroadeningIntegral
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Compact domination for the finite-cutoff Born-Dyson current rung

This module discharges the measure-theoretic domination hypotheses used by the zero-broadening
radial-integral bridge from compact radial nonvanishing of the boundary retarded-advanced
denominator. The finite-`η` radial dependence of each quadratic Dyson denominator differs from its
boundary by a momentum-independent offset, so fixed-momentum convergence at `p = 0` supplies uniform
control on the whole finite interval.

The cutoff and disorder strength remain fixed. No weak-disorder, ultraviolet, solved-ladder,
conductivity, or simultaneous-limit statement is introduced here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter MeasureTheory Set
open QuantumTheory.Transport

private theorem continuous_boundaryBornDysonDenominator_radial
    (side : SpectralSide)
    (v m probeEnergy disorderStrength hbar pMax : ℝ) :
    Continuous (fun p : ℝ =>
      finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
        side v m p probeEnergy disorderStrength hbar pMax) := by
  unfold finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
  fun_prop

private theorem continuous_finiteBroadeningBornCurrentRungRadialIntegrand
    (i j : Direction2)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    Continuous (fun p : ℝ =>
      finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand
        i j v m p probeEnergy broadening disorderStrength hbar pMax) := by
  have hdenContinuous :
      Continuous (fun p : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
          v m p probeEnergy broadening disorderStrength hbar pMax) := by
    unfold finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
      finiteCutoffContinuumBornDysonDenominator
    fun_prop
  have hdenNe : ∀ p : ℝ,
      finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
        v m p probeEnergy broadening disorderStrength hbar pMax ≠ 0 := fun p =>
    finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct_ne_zero
      v m p probeEnergy broadening disorderStrength hbar pMax
      hbroadening hdisorder hpMax
  have hinv :
      Continuous (fun p : ℝ =>
        (finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
          v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹) :=
    hdenContinuous.inv₀ hdenNe
  have hangular :
      Continuous (fun p : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficient
          i j v m p probeEnergy broadening disorderStrength hbar pMax) := by
    rw [show
      (fun p : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficient
          i j v m p probeEnergy broadening disorderStrength hbar pMax) =
      (fun p : ℝ =>
        (((2 * Real.pi : ℝ) : ℂ)) *
          (finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
            v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹ *
          finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumerator
            i j v m probeEnergy broadening disorderStrength hbar pMax) by
        funext p
        rw [finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficient_eq_denominatorForm]]
    exact (continuous_const.mul hinv).mul continuous_const
  exact
    ((continuous_const.mul (Complex.continuous_ofReal.comp continuous_id)).mul hangular)

/-- If the fixed-cutoff zero-broadening RA denominator product is nonzero on the whole radial
interval, the normalized finite-cutoff current-rung integral converges as `η → 0⁺` without requiring
callers to supply separate measurability or domination hypotheses. -/
theorem tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient_broadening_zero_of_boundary_denominator_nonzero
    (i j : Direction2)
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hpMax : 0 ≤ pMax) (hdisorder : 0 ≤ disorderStrength)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2)
    (hden : ∀ p ∈ Set.Icc (0 : ℝ) pMax,
      finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary
        v m p probeEnergy disorderStrength hbar pMax ≠ 0) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient
          i j v m probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficientZeroBroadeningBoundary
          i j v m probeEnergy disorderStrength hbar pMax)) := by
  have hdenR : ∀ p ∈ Set.Icc (0 : ℝ) pMax,
      finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
        .retarded v m p probeEnergy disorderStrength hbar pMax ≠ 0 := by
    intro p hp hzero
    apply hden p hp
    unfold finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary
    rw [hzero]
    simp
  have hdenA : ∀ p ∈ Set.Icc (0 : ℝ) pMax,
      finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
        .advanced v m p probeEnergy disorderStrength hbar pMax ≠ 0 := by
    intro p hp hzero
    apply hden p hp
    unfold finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary
    rw [hzero]
    simp
  have hcontR : Continuous (fun p : ℝ =>
      ‖finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
        .retarded v m p probeEnergy disorderStrength hbar pMax‖) :=
    (continuous_boundaryBornDysonDenominator_radial
      .retarded v m probeEnergy disorderStrength hbar pMax).norm
  have hcontA : Continuous (fun p : ℝ =>
      ‖finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
        .advanced v m p probeEnergy disorderStrength hbar pMax‖) :=
    (continuous_boundaryBornDysonDenominator_radial
      .advanced v m probeEnergy disorderStrength hbar pMax).norm
  obtain ⟨pR, hpR, hminR⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hpMax) hcontR.continuousOn
  obtain ⟨pA, hpA, hminA⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hpMax) hcontA.continuousOn
  let δR : ℝ :=
    ‖finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
      .retarded v m pR probeEnergy disorderStrength hbar pMax‖
  let δA : ℝ :=
    ‖finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
      .advanced v m pA probeEnergy disorderStrength hbar pMax‖
  have hδR : 0 < δR := by
    dsimp [δR]
    exact norm_pos_iff.mpr (hdenR pR hpR)
  have hδA : 0 < δA := by
    dsimp [δA]
    exact norm_pos_iff.mpr (hdenA pA hpA)
  have hRzero :=
    tendsto_finiteCutoffContinuumBornDysonDenominator_broadening_zero
      .retarded v m 0 probeEnergy disorderStrength hbar pMax
      hvelocity hmetal hcutoff
  have hAzero :=
    tendsto_finiteCutoffContinuumBornDysonDenominator_broadening_zero
      .advanced v m 0 probeEnergy disorderStrength hbar pMax
      hvelocity hmetal hcutoff
  have hRclose :
      ∀ᶠ broadening : ℝ in nhdsWithin 0 (Set.Ioi 0),
        dist
          (finiteCutoffContinuumBornDysonDenominator
            .retarded v m 0 0 probeEnergy broadening disorderStrength hbar pMax)
          (finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
            .retarded v m 0 probeEnergy disorderStrength hbar pMax) < δR / 2 :=
    (Metric.tendsto_nhds.1 hRzero) (δR / 2) (half_pos hδR)
  have hAclose :
      ∀ᶠ broadening : ℝ in nhdsWithin 0 (Set.Ioi 0),
        dist
          (finiteCutoffContinuumBornDysonDenominator
            .advanced v m 0 0 probeEnergy broadening disorderStrength hbar pMax)
          (finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
            .advanced v m 0 probeEnergy disorderStrength hbar pMax) < δA / 2 :=
    (Metric.tendsto_nhds.1 hAzero) (δA / 2) (half_pos hδA)
  let numeratorBoundary : ℂ :=
    finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumeratorZeroBroadeningBoundary
      i j v m probeEnergy disorderStrength hbar pMax
  have hnum :=
    tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumerator_broadening_zero
      i j v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hnumClose :
      ∀ᶠ broadening : ℝ in nhdsWithin 0 (Set.Ioi 0),
        dist
          (finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumerator
            i j v m probeEnergy broadening disorderStrength hbar pMax)
          numeratorBoundary < 1 := by
    simpa [numeratorBoundary] using (Metric.tendsto_nhds.1 hnum) 1 zero_lt_one
  let cR : ℝ := δR / 2
  let cA : ℝ := δA / 2
  let cDen : ℝ := cR * cA
  let boundValue : ℝ :=
    ‖(((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ))‖ * pMax *
      ‖(((2 * Real.pi : ℝ) : ℂ))‖ * cDen⁻¹ * (‖numeratorBoundary‖ + 1)
  have hcR : 0 < cR := by dsimp [cR]; exact half_pos hδR
  have hcA : 0 < cA := by dsimp [cA]; exact half_pos hδA
  have hcDen : 0 < cDen := mul_pos hcR hcA
  have hMeasurable :
      ∀ᶠ broadening : ℝ in nhdsWithin 0 (Set.Ioi 0),
        AEStronglyMeasurable
          (fun p =>
            finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand
              i j v m p probeEnergy broadening disorderStrength hbar pMax)
          (volume.restrict (Set.Icc 0 pMax)) := by
    filter_upwards [self_mem_nhdsWithin] with broadening hbroadening
    have hcontinuous :=
      continuous_finiteBroadeningBornCurrentRungRadialIntegrand
        i j v m probeEnergy broadening disorderStrength hbar pMax
        (ne_of_gt hbroadening) hdisorder hpMax
    exact hcontinuous.stronglyMeasurable.aestronglyMeasurable
  have hBound :
      ∀ᶠ broadening : ℝ in nhdsWithin 0 (Set.Ioi 0),
        ∀ᵐ p ∂(volume.restrict (Set.Icc 0 pMax)),
          ‖finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand
              i j v m p probeEnergy broadening disorderStrength hbar pMax‖ ≤ boundValue := by
    filter_upwards [self_mem_nhdsWithin, hRclose, hAclose, hnumClose] with
      broadening hbroadening hRcloseAt hAcloseAt hnumCloseAt
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc ?_
    intro p hp
    let DR0 := finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
      .retarded v m p probeEnergy disorderStrength hbar pMax
    let DA0 := finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
      .advanced v m p probeEnergy disorderStrength hbar pMax
    let DR := finiteCutoffContinuumBornDysonDenominator
      .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let DA := finiteCutoffContinuumBornDysonDenominator
      .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
    have hdiffR :
        DR - DR0 =
          finiteCutoffContinuumBornDysonDenominator
              .retarded v m 0 0 probeEnergy broadening disorderStrength hbar pMax -
            finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
              .retarded v m 0 probeEnergy disorderStrength hbar pMax := by
      dsimp [DR, DR0]
      unfold finiteCutoffContinuumBornDysonDenominator
        finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
      ring_nf
    have hdiffA :
        DA - DA0 =
          finiteCutoffContinuumBornDysonDenominator
              .advanced v m 0 0 probeEnergy broadening disorderStrength hbar pMax -
            finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
              .advanced v m 0 probeEnergy disorderStrength hbar pMax := by
      dsimp [DA, DA0]
      unfold finiteCutoffContinuumBornDysonDenominator
        finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
      ring_nf
    have herrR : ‖DR - DR0‖ < cR := by
      rw [hdiffR]
      simpa [cR, dist_eq_norm] using hRcloseAt
    have herrA : ‖DA - DA0‖ < cA := by
      rw [hdiffA]
      simpa [cA, dist_eq_norm] using hAcloseAt
    have htriR : ‖DR0‖ ≤ ‖DR - DR0‖ + ‖DR‖ := by
      calc
        ‖DR0‖ = ‖(DR0 - DR) + DR‖ := by ring_nf
        _ ≤ ‖DR0 - DR‖ + ‖DR‖ := norm_add_le _ _
        _ = ‖DR - DR0‖ + ‖DR‖ := by rw [norm_sub_rev]
    have htriA : ‖DA0‖ ≤ ‖DA - DA0‖ + ‖DA‖ := by
      calc
        ‖DA0‖ = ‖(DA0 - DA) + DA‖ := by ring_nf
        _ ≤ ‖DA0 - DA‖ + ‖DA‖ := norm_add_le _ _
        _ = ‖DA - DA0‖ + ‖DA‖ := by rw [norm_sub_rev]
    have hRlower : cR ≤ ‖DR‖ := by
      have hmin := hminR hp
      dsimp [δR] at hmin
      dsimp [DR0]
      dsimp [cR]
      linarith
    have hAlower : cA ≤ ‖DA‖ := by
      have hmin := hminA hp
      dsimp [δA] at hmin
      dsimp [DA0]
      dsimp [cA]
      linarith
    have hproductNorm :
        ‖finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
          v m p probeEnergy broadening disorderStrength hbar pMax‖ = ‖DR‖ * ‖DA‖ := by
      dsimp [DR, DA]
      simp [finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct]
    have hproductLower :
        cDen ≤
          ‖finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
            v m p probeEnergy broadening disorderStrength hbar pMax‖ := by
      rw [hproductNorm]
      dsimp [cDen]
      exact mul_le_mul hRlower hAlower (le_of_lt hcA) (norm_nonneg _)
    have hproductPos :
        0 < ‖finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
          v m p probeEnergy broadening disorderStrength hbar pMax‖ :=
      lt_of_lt_of_le hcDen hproductLower
    have hinvBound :
        ‖(finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
          v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹‖ ≤ cDen⁻¹ := by
      rw [norm_inv]
      exact (inv_le_inv₀ hproductPos hcDen).2 hproductLower
    have hnumErr :
        ‖finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumerator
              i j v m probeEnergy broadening disorderStrength hbar pMax - numeratorBoundary‖ < 1 := by
      simpa [dist_eq_norm] using hnumCloseAt
    have hnumTri :
        ‖finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumerator
            i j v m probeEnergy broadening disorderStrength hbar pMax‖ ≤
          ‖finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumerator
              i j v m probeEnergy broadening disorderStrength hbar pMax - numeratorBoundary‖ +
            ‖numeratorBoundary‖ := by
      calc
        ‖finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumerator
            i j v m probeEnergy broadening disorderStrength hbar pMax‖ =
            ‖(finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumerator
                i j v m probeEnergy broadening disorderStrength hbar pMax - numeratorBoundary) +
              numeratorBoundary‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    have hnumBound :
        ‖finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumerator
            i j v m probeEnergy broadening disorderStrength hbar pMax‖ ≤
          ‖numeratorBoundary‖ + 1 := by
      linarith
    have hpNorm : ‖(p : ℂ)‖ ≤ pMax := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp.1]
      exact hp.2
    rw [finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand,
      finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficient_eq_denominatorForm]
    simp only [norm_mul]
    dsimp [boundValue]
    let prefNorm : ℝ := ‖(((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ))‖
    let angleNorm : ℝ := ‖(((2 * Real.pi : ℝ) : ℂ))‖
    let invNorm : ℝ :=
      ‖(finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
        v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹‖
    let numNorm : ℝ :=
      ‖finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumerator
        i j v m probeEnergy broadening disorderStrength hbar pMax‖
    have hpref : 0 ≤ prefNorm := norm_nonneg _
    have hangle : 0 ≤ angleNorm := norm_nonneg _
    have hinv : 0 ≤ invNorm := norm_nonneg _
    have hnum : 0 ≤ numNorm := norm_nonneg _
    have hcDenInv : 0 ≤ cDen⁻¹ := (inv_pos.mpr hcDen).le
    have hnumBoundary : 0 ≤ ‖numeratorBoundary‖ + 1 := by positivity
    have h1 : prefNorm * ‖(p : ℂ)‖ * angleNorm * invNorm * numNorm ≤
        prefNorm * pMax * angleNorm * invNorm * numNorm := by
      have h := mul_le_mul_of_nonneg_left hpNorm hpref
      have h := mul_le_mul_of_nonneg_right h hangle
      have h := mul_le_mul_of_nonneg_right h hinv
      exact mul_le_mul_of_nonneg_right h hnum
    have h2 : prefNorm * pMax * angleNorm * invNorm * numNorm ≤
        prefNorm * pMax * angleNorm * cDen⁻¹ * numNorm := by
      have hleft : 0 ≤ prefNorm * pMax * angleNorm := by positivity
      have h := mul_le_mul_of_nonneg_left hinvBound hleft
      exact mul_le_mul_of_nonneg_right h hnum
    have h3 : prefNorm * pMax * angleNorm * cDen⁻¹ * numNorm ≤
        prefNorm * pMax * angleNorm * cDen⁻¹ * (‖numeratorBoundary‖ + 1) := by
      have hleft : 0 ≤ prefNorm * pMax * angleNorm * cDen⁻¹ := by positivity
      exact mul_le_mul_of_nonneg_left hnumBound hleft
    change prefNorm * ‖(p : ℂ)‖ * angleNorm * invNorm * numNorm ≤
      prefNorm * pMax * angleNorm * cDen⁻¹ * (‖numeratorBoundary‖ + 1)
    exact h1.trans (h2.trans h3)
  have hBoundIntegrable :
      Integrable (fun _ : ℝ => boundValue) (volume.restrict (Set.Icc 0 pMax)) := by
    exact integrableOn_const isCompact_Icc.measure_lt_top.ne
  exact
    tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient_broadening_zero_of_dominated
      i j v m probeEnergy disorderStrength hbar pMax hpMax hvelocity hmetal hcutoff hden
      (fun _ => boundValue) hMeasurable hBound hBoundIntegrable

end

end QuantumTheory.Transport.Models.MassiveDirac
