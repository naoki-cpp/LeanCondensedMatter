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

/-- Canonical zero-broadening boundary of the source-`σₓ` current rung. -/
noncomputable def finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : InPlaneCoefficientVector :=
  fun output =>
    finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficientZeroBroadeningBoundary
      output .x v m probeEnergy disorderStrength hbar pMax

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

theorem continuous_finiteBroadeningBornCurrentRungRadialIntegrand
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
  have hangularEq :
      (fun p : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficient
          i j v m p probeEnergy broadening disorderStrength hbar pMax) =
      (fun p : ℝ =>
        (((2 * Real.pi : ℝ) : ℂ)) *
          (finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
            v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹ *
          finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumerator
            i j v m probeEnergy broadening disorderStrength hbar pMax) := by
    funext p
    rw [finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficient_eq_denominatorForm]
  have hangular :
      Continuous (fun p : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficient
          i j v m p probeEnergy broadening disorderStrength hbar pMax) := by
    rw [hangularEq]
    exact (continuous_const.mul hinv).mul continuous_const
  exact
    ((continuous_const.mul (Complex.continuous_ofReal.comp continuous_id)).mul hangular)

private theorem boundaryBornDysonDenominator_ne_zero_of_product_ne_zero
    (side : SpectralSide)
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hden : ∀ p ∈ Set.Icc (0 : ℝ) pMax,
      finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary
        v m p probeEnergy disorderStrength hbar pMax ≠ 0) :
    ∀ p ∈ Set.Icc (0 : ℝ) pMax,
      finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
        side v m p probeEnergy disorderStrength hbar pMax ≠ 0 := by
  intro p hp hzero
  apply hden p hp
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary
  cases side <;> simp [hzero]

private theorem finiteCutoffContinuumBornDysonDenominator_sub_boundary_eq_zeroMomentum
    (side : SpectralSide)
    (v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonDenominator
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax -
        finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
          side v m p probeEnergy disorderStrength hbar pMax =
      finiteCutoffContinuumBornDysonDenominator
          side v m 0 0 probeEnergy broadening disorderStrength hbar pMax -
        finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
          side v m 0 probeEnergy disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornDysonDenominator
    finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
  ring_nf

private theorem eventually_norm_finiteCutoffContinuumBornDysonDenominator_lower_bound
    (side : SpectralSide)
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hpMax : 0 ≤ pMax) (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2)
    (hden : ∀ p ∈ Set.Icc (0 : ℝ) pMax,
      finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
        side v m p probeEnergy disorderStrength hbar pMax ≠ 0) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ broadening : ℝ in nhdsWithin 0 (Set.Ioi 0),
        ∀ p ∈ Set.Icc (0 : ℝ) pMax,
          c ≤ ‖finiteCutoffContinuumBornDysonDenominator
            side v m p 0 probeEnergy broadening disorderStrength hbar pMax‖ := by
  have hcont : Continuous (fun p : ℝ =>
      ‖finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
        side v m p probeEnergy disorderStrength hbar pMax‖) :=
    (continuous_boundaryBornDysonDenominator_radial
      side v m probeEnergy disorderStrength hbar pMax).norm
  obtain ⟨pMin, hpMin, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hpMax) hcont.continuousOn
  let δ : ℝ :=
    ‖finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
      side v m pMin probeEnergy disorderStrength hbar pMax‖
  have hδ : 0 < δ := by
    dsimp [δ]
    exact norm_pos_iff.mpr (hden pMin hpMin)
  have hzero :=
    tendsto_finiteCutoffContinuumBornDysonDenominator_broadening_zero
      side v m 0 probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hclose :
      ∀ᶠ broadening : ℝ in nhdsWithin 0 (Set.Ioi 0),
        dist
          (finiteCutoffContinuumBornDysonDenominator
            side v m 0 0 probeEnergy broadening disorderStrength hbar pMax)
          (finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
            side v m 0 probeEnergy disorderStrength hbar pMax) < δ / 2 :=
    (Metric.tendsto_nhds.1 hzero) (δ / 2) (half_pos hδ)
  let c : ℝ := δ / 2
  refine ⟨c, by dsimp [c]; exact half_pos hδ, ?_⟩
  filter_upwards [hclose] with broadening hcloseAt
  intro p hp
  let D0 := finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
    side v m p probeEnergy disorderStrength hbar pMax
  let D := finiteCutoffContinuumBornDysonDenominator
    side v m p 0 probeEnergy broadening disorderStrength hbar pMax
  have hdiff :
      D - D0 =
        finiteCutoffContinuumBornDysonDenominator
            side v m 0 0 probeEnergy broadening disorderStrength hbar pMax -
          finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
            side v m 0 probeEnergy disorderStrength hbar pMax := by
    dsimp [D, D0]
    exact finiteCutoffContinuumBornDysonDenominator_sub_boundary_eq_zeroMomentum
      side v m p probeEnergy broadening disorderStrength hbar pMax
  have herr : ‖D - D0‖ < c := by
    rw [hdiff]
    simpa [c, dist_eq_norm] using hcloseAt
  have htri : ‖D0‖ ≤ ‖D - D0‖ + ‖D‖ := by
    calc
      ‖D0‖ = ‖(D0 - D) + D‖ := by ring_nf
      _ ≤ ‖D0 - D‖ + ‖D‖ := norm_add_le _ _
      _ = ‖D - D0‖ + ‖D‖ := by rw [norm_sub_rev]
  have hboundaryLower : δ ≤ ‖D0‖ := by
    simpa [δ, D0] using hmin hp
  dsimp [c] at herr ⊢
  linarith [hboundaryLower, htri]

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
  have hdenR := boundaryBornDysonDenominator_ne_zero_of_product_ne_zero
    .retarded v m probeEnergy disorderStrength hbar pMax hden
  have hdenA := boundaryBornDysonDenominator_ne_zero_of_product_ne_zero
    .advanced v m probeEnergy disorderStrength hbar pMax hden
  obtain ⟨cR, hcR, hRlower⟩ :=
    eventually_norm_finiteCutoffContinuumBornDysonDenominator_lower_bound
      .retarded v m probeEnergy disorderStrength hbar pMax
      hpMax hvelocity hmetal hcutoff hdenR
  obtain ⟨cA, hcA, hAlower⟩ :=
    eventually_norm_finiteCutoffContinuumBornDysonDenominator_lower_bound
      .advanced v m probeEnergy disorderStrength hbar pMax
      hpMax hvelocity hmetal hcutoff hdenA
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
  let cDen : ℝ := cR * cA
  let boundValue : ℝ :=
    ‖(((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ))‖ * pMax *
      ‖(((2 * Real.pi : ℝ) : ℂ))‖ * cDen⁻¹ * (‖numeratorBoundary‖ + 1)
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
    filter_upwards [self_mem_nhdsWithin, hRlower, hAlower, hnumClose] with
      broadening hbroadening hRlowerAt hAlowerAt hnumCloseAt
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc ?_
    intro p hp
    let DR := finiteCutoffContinuumBornDysonDenominator
      .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let DA := finiteCutoffContinuumBornDysonDenominator
      .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
    have hRlowerAt' : cR ≤ ‖DR‖ := by
      simpa [DR] using hRlowerAt p hp
    have hAlowerAt' : cA ≤ ‖DA‖ := by
      simpa [DA] using hAlowerAt p hp
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
      exact mul_le_mul hRlowerAt' hAlowerAt' (le_of_lt hcA) (norm_nonneg _)
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

theorem finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary_ne_zero
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

/-- The finite-`η` canonical current-rung vector converges to its fixed-disorder zero-broadening
boundary. -/
theorem tendsto_finiteCutoffContinuumBornDysonCurrentRungVector_broadening_zero_of_boundary_realRenormalization_lt_one
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hpMax : 0 ≤ pMax) (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hdisorder : 0 < disorderStrength) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2)
    (hrenorm :
      finiteCutoffContinuumBornBoundaryRealRenormalization
        v m probeEnergy disorderStrength hbar pMax < 1) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornDysonCurrentRungVector
          v m probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary
          v m probeEnergy disorderStrength hbar pMax)) := by
  rw [tendsto_pi_nhds]
  intro output
  simpa [finiteCutoffContinuumBornDysonCurrentRungVector,
    finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary] using
    tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient_broadening_zero_of_boundary_realRenormalization_lt_one
      output .x v m probeEnergy disorderStrength hbar pMax
      hpMax hvelocity hhbar hdisorder hmetal hcutoff hrenorm

end

end QuantumTheory.Transport.Models.MassiveDirac
