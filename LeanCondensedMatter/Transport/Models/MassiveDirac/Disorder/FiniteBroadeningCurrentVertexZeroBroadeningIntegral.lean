import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertexZeroBroadening
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Zero-broadening finite-cutoff Born-Dyson current-rung integrals

The fixed-radial-momentum `η → 0⁺` limits are owned upstream by
`FiniteBroadeningCurrentVertexZeroBroadening`. This module owns the integrated boundary: the generic
dominated-convergence bridge, compact domination from a nonvanishing boundary denominator, and the
model-specific real-renormalization condition that discharges that nonvanishing hypothesis.

The cutoff and disorder strength remain fixed. No weak-disorder, ultraviolet, solved-ladder,
conductivity, or simultaneous-limit statement is introduced here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter MeasureTheory Set
open QuantumTheory.Transport
open scoped Interval

/-- Zero-broadening boundary of normalized finite-cutoff current-rung entry `(i,j)`. -/
noncomputable def finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficientZeroBroadeningBoundary
    (i j : Direction2)
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  ∫ p in (0 : ℝ)..pMax,
    finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrandZeroBroadeningBoundary
      i j v m p probeEnergy disorderStrength hbar pMax

/-- Dominated convergence passes `η → 0⁺` through any normalized finite radial current-rung entry
once one integrable radial bound, eventual strong measurability, and nonvanishing of the boundary RA
denominator on the compact radial interval are supplied. -/
theorem tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient_broadening_zero_of_dominated
    (i j : Direction2)
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hpMax : 0 ≤ pMax)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2)
    (hden : ∀ p ∈ Set.Icc (0 : ℝ) pMax,
      finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary
        v m p probeEnergy disorderStrength hbar pMax ≠ 0)
    (bound : ℝ → ℝ)
    (hMeasurable :
      ∀ᶠ broadening : ℝ in nhdsWithin 0 (Set.Ioi 0),
        AEStronglyMeasurable
          (fun p =>
            finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand
              i j v m p probeEnergy broadening disorderStrength hbar pMax)
          (volume.restrict (Set.Icc 0 pMax)))
    (hBound :
      ∀ᶠ broadening : ℝ in nhdsWithin 0 (Set.Ioi 0),
        ∀ᵐ p ∂(volume.restrict (Set.Icc 0 pMax)),
          ‖finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand
              i j v m p probeEnergy broadening disorderStrength hbar pMax‖ ≤ bound p)
    (hBoundIntegrable : Integrable bound (volume.restrict (Set.Icc 0 pMax))) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient
          i j v m probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficientZeroBroadeningBoundary
          i j v m probeEnergy disorderStrength hbar pMax)) := by
  have hpointwise :
      ∀ᵐ p ∂(volume.restrict (Set.Icc 0 pMax)),
        Tendsto
          (fun broadening : ℝ =>
            finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand
              i j v m p probeEnergy broadening disorderStrength hbar pMax)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrandZeroBroadeningBoundary
              i j v m p probeEnergy disorderStrength hbar pMax)) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun p hp =>
      tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand_broadening_zero
        i j v m p probeEnergy disorderStrength hbar pMax
        hvelocity hmetal hcutoff (hden p hp))
  have hset := tendsto_integral_filter_of_dominated_convergence
    bound hMeasurable hBound hBoundIntegrable hpointwise
  have hfinite :
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient
          i j v m probeEnergy broadening disorderStrength hbar pMax) =
      (fun broadening : ℝ =>
        ∫ p in Set.Icc (0 : ℝ) pMax,
          finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand
            i j v m p probeEnergy broadening disorderStrength hbar pMax) := by
    funext broadening
    unfold finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient
    rw [intervalIntegral.integral_of_le hpMax]
    rw [← MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hboundary :
      finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficientZeroBroadeningBoundary
          i j v m probeEnergy disorderStrength hbar pMax =
        ∫ p in Set.Icc (0 : ℝ) pMax,
          finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrandZeroBroadeningBoundary
            i j v m p probeEnergy disorderStrength hbar pMax := by
    unfold finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficientZeroBroadeningBoundary
    rw [intervalIntegral.integral_of_le hpMax]
    rw [← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [hfinite, hboundary]
  exact hset

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
    have hRboundaryLower : δR ≤ ‖DR0‖ := by
      simpa [δR, DR0] using hminR hp
    have hAboundaryLower : δA ≤ ‖DA0‖ := by
      simpa [δA, DA0] using hminA hp
    have hRlower : cR ≤ ‖DR‖ := by
      dsimp [cR] at herrR ⊢
      linarith [hRboundaryLower, htriR]
    have hAlower : cA ≤ ‖DA‖ := by
      dsimp [cA] at herrA ⊢
      linarith [hAboundaryLower, htriA]
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
    have hcDenInv : 0 ≤ cDen⁻¹ := (inv_pos.mpr hcDen).le
    have hinvNum :
        ‖(finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
              v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹‖ *
            ‖finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumerator
              i j v m probeEnergy broadening disorderStrength hbar pMax‖ ≤
          cDen⁻¹ * (‖numeratorBoundary‖ + 1) := by
      exact mul_le_mul hinvBound hnumBound (norm_nonneg _) hcDenInv
    have hangularBound :
        ‖(((2 * Real.pi : ℝ) : ℂ))‖ *
            ‖(finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
              v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹‖ *
            ‖finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumerator
              i j v m probeEnergy broadening disorderStrength hbar pMax‖ ≤
          ‖(((2 * Real.pi : ℝ) : ℂ))‖ * cDen⁻¹ * (‖numeratorBoundary‖ + 1) := by
      simpa [mul_assoc] using
        (mul_le_mul_of_nonneg_left hinvNum (norm_nonneg (((2 * Real.pi : ℝ) : ℂ))))
    have hprefP :
        ‖(((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ))‖ * ‖(p : ℂ)‖ ≤
          ‖(((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ))‖ * pMax :=
      mul_le_mul_of_nonneg_left hpNorm (norm_nonneg _)
    have hradial :
        (‖(((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ))‖ * ‖(p : ℂ)‖) *
            (‖(((2 * Real.pi : ℝ) : ℂ))‖ *
              ‖(finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
                v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹‖ *
              ‖finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumerator
                i j v m probeEnergy broadening disorderStrength hbar pMax‖) ≤
          (‖(((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ))‖ * pMax) *
            (‖(((2 * Real.pi : ℝ) : ℂ))‖ * cDen⁻¹ * (‖numeratorBoundary‖ + 1)) := by
      calc
        _ ≤ (‖(((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ))‖ * pMax) *
            (‖(((2 * Real.pi : ℝ) : ℂ))‖ *
              ‖(finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
                v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹‖ *
              ‖finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumerator
                i j v m probeEnergy broadening disorderStrength hbar pMax‖) :=
          mul_le_mul_of_nonneg_right hprefP (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left hangularBound (by positivity)
    simpa [mul_assoc] using hradial
  have hBoundIntegrable :
      Integrable (fun _ : ℝ => boundValue) (volume.restrict (Set.Icc 0 pMax)) := by
    exact integrableOn_const isCompact_Icc.measure_lt_top.ne
  exact
    tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient_broadening_zero_of_dominated
      i j v m probeEnergy disorderStrength hbar pMax hpMax hvelocity hmetal hcutoff hden
      (fun _ => boundValue) hMeasurable hBound hBoundIntegrable

/-- Dimensionless real finite-cutoff Born renormalization entering the zero-broadening effective
energy and mass. The real part is intentional here: this quantity tracks the real self-energy shift,
not a conversion from a complex observable to a real one. -/
def finiteCutoffContinuumBornBoundaryRealRenormalization
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℝ :=
  (disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
    (finiteCutoffContinuumBornDenominatorIntegralBoundaryValue
      .retarded v m probeEnergy pMax).re

private theorem finiteCutoffContinuumBornBoundaryRealRenormalization_eq_side
    (side : SpectralSide)
    (v m probeEnergy disorderStrength hbar pMax : ℝ) :
    (disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
        (finiteCutoffContinuumBornDenominatorIntegralBoundaryValue
          side v m probeEnergy pMax).re =
      finiteCutoffContinuumBornBoundaryRealRenormalization
        v m probeEnergy disorderStrength hbar pMax := by
  cases side <;>
    simp [finiteCutoffContinuumBornBoundaryRealRenormalization,
      finiteCutoffContinuumBornDenominatorIntegralBoundaryValue,
      pauliGreenDenominator, SpectralSide.regulator]

private theorem finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary_im_eq
    (side : SpectralSide)
    (v m p probeEnergy disorderStrength hbar pMax : ℝ) :
    (finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
      side v m p probeEnergy disorderStrength hbar pMax).im =
      -2 * (disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
        (finiteCutoffContinuumBornDenominatorIntegralBoundaryValue
          side v m probeEnergy pMax).im *
        (probeEnergy ^ 2 + m ^ 2 -
          (disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
            (finiteCutoffContinuumBornDenominatorIntegralBoundaryValue
              side v m probeEnergy pMax).re *
            (probeEnergy ^ 2 - m ^ 2)) := by
  unfold finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
    finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary
    finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary
  simp only [pow_two, Complex.sub_im, Complex.sub_re, Complex.add_im, Complex.add_re,
    Complex.mul_im, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, zero_mul,
    add_zero, zero_add]
  ring

private theorem continuumBornAngularMeasurePrefactor_pos
    (hbar : ℝ) (hhbar : hbar ≠ 0) :
    0 < continuumBornAngularMeasurePrefactor hbar := by
  unfold continuumBornAngularMeasurePrefactor momentumMeasurePrefactor
  have hden : 0 < (2 * Real.pi * hbar) ^ 2 :=
    sq_pos_of_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hhbar)
  exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (one_div_pos.mpr hden)

private theorem finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary_ne_zero
    (side : SpectralSide)
    (v m p probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hdisorder : 0 < disorderStrength) (hmetal : |m| < probeEnergy)
    (hrenorm :
      finiteCutoffContinuumBornBoundaryRealRenormalization
        v m probeEnergy disorderStrength hbar pMax < 1) :
    finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
      side v m p probeEnergy disorderStrength hbar pMax ≠ 0 := by
  have hprobe : 0 < probeEnergy := lt_of_le_of_lt (abs_nonneg m) hmetal
  have hmetalSq : m ^ 2 < probeEnergy ^ 2 := by
    rw [← sq_abs m]
    nlinarith [abs_nonneg m]
  have hgap : 0 < probeEnergy ^ 2 - m ^ 2 := sub_pos.mpr hmetalSq
  have hmeasure : 0 < continuumBornAngularMeasurePrefactor hbar :=
    continuumBornAngularMeasurePrefactor_pos hbar hhbar
  have hg :
      0 < disorderStrength * continuumBornAngularMeasurePrefactor hbar :=
    mul_pos hdisorder hmeasure
  let J : ℂ :=
    finiteCutoffContinuumBornDenominatorIntegralBoundaryValue
      side v m probeEnergy pMax
  let lambda : ℝ :=
    (disorderStrength * continuumBornAngularMeasurePrefactor hbar) * J.re
  have hlambda : lambda < 1 := by
    dsimp [lambda, J]
    rw [finiteCutoffContinuumBornBoundaryRealRenormalization_eq_side]
    exact hrenorm
  have hlambdaGap :
      lambda * (probeEnergy ^ 2 - m ^ 2) < probeEnergy ^ 2 - m ^ 2 := by
    simpa using mul_lt_mul_of_pos_right hlambda hgap
  have hbracket :
      0 < probeEnergy ^ 2 + m ^ 2 - lambda * (probeEnergy ^ 2 - m ^ 2) := by
    nlinarith [hlambdaGap, sq_nonneg m]
  have hJim : J.im ≠ 0 := by
    dsimp [J]
    rw [finiteCutoffContinuumBornDenominatorIntegralBoundaryValue_im]
    have hvSq : v ^ 2 ≠ 0 := pow_ne_zero 2 hvelocity
    have htwoVSq : (2 * v ^ 2) ≠ 0 := mul_ne_zero (by norm_num) hvSq
    have hinv : ((2 * v ^ 2)⁻¹ : ℝ) ≠ 0 := inv_ne_zero htwoVSq
    have hsign : side.sign ≠ 0 := by
      cases side <;> simp [SpectralSide.sign]
    exact mul_ne_zero (neg_ne_zero.mpr hinv) (mul_ne_zero hsign Real.pi_ne_zero)
  have himNe :
      (finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
        side v m p probeEnergy disorderStrength hbar pMax).im ≠ 0 := by
    rw [finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary_im_eq]
    change
      -2 * (disorderStrength * continuumBornAngularMeasurePrefactor hbar) * J.im *
        (probeEnergy ^ 2 + m ^ 2 - lambda * (probeEnergy ^ 2 - m ^ 2)) ≠ 0
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt hg)) hJim)
      (ne_of_gt hbracket)
  intro hzero
  apply himNe
  simpa using congrArg Complex.im hzero

private theorem finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary_ne_zero
    (v m p probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hdisorder : 0 < disorderStrength) (hmetal : |m| < probeEnergy)
    (hrenorm :
      finiteCutoffContinuumBornBoundaryRealRenormalization
        v m probeEnergy disorderStrength hbar pMax < 1) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary
      v m p probeEnergy disorderStrength hbar pMax ≠ 0 := by
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary
  exact mul_ne_zero
    (finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary_ne_zero
      .retarded v m p probeEnergy disorderStrength hbar pMax
      hvelocity hhbar hdisorder hmetal hrenorm)
    (finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary_ne_zero
      .advanced v m p probeEnergy disorderStrength hbar pMax
      hvelocity hhbar hdisorder hmetal hrenorm)

/-- At fixed finite cutoff and fixed positive disorder strength, the normalized Born-Dyson current
rung has its `η → 0⁺` integral boundary when the real Born renormalization remains below one. This
condition keeps the boundary retarded/advanced denominator off zero through its side-indexed damping
component, thereby discharging the compact nonvanishing hypothesis required by dominated
convergence. -/
theorem tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient_broadening_zero_of_boundary_realRenormalization_lt_one
    (i j : Direction2)
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hpMax : 0 ≤ pMax) (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hdisorder : 0 < disorderStrength) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2)
    (hrenorm :
      finiteCutoffContinuumBornBoundaryRealRenormalization
        v m probeEnergy disorderStrength hbar pMax < 1) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient
          i j v m probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficientZeroBroadeningBoundary
          i j v m probeEnergy disorderStrength hbar pMax)) := by
  apply
    tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient_broadening_zero_of_boundary_denominator_nonzero
      i j v m probeEnergy disorderStrength hbar pMax hpMax hdisorder.le
      hvelocity hmetal hcutoff
  intro p _
  exact
    finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary_ne_zero
      v m p probeEnergy disorderStrength hbar pMax
      hvelocity hhbar hdisorder hmetal hrenorm

end

end QuantumTheory.Transport.Models.MassiveDirac
