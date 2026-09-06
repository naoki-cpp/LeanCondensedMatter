import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertexZeroBroadening
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Radial zero-broadening boundary of the finite-eta Born-Dyson current rung

This module upgrades the fixed-radial-momentum positive-broadening boundary of the normalized
Born-Dyson current-rung integrands to the finite-cutoff radial integrals. The analytic regularity
required for the inverse is kept explicit as a uniform inverse bound for the retarded-advanced
denominator product on the compact radial interval near `η = 0⁺`.

No solved-ladder limit, Hall insertion, disorder-strength limit, ultraviolet removal, or mechanism
label is introduced here. The repository orientation remains `Gᴿ Γ Gᴬ`.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter MeasureTheory
open QuantumTheory.Transport
open scoped Interval

/-- Zero-broadening boundary of the finite-cutoff normalized longitudinal current-rung coefficient. -/
noncomputable def finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficientZeroBroadeningBoundary
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  ∫ p in (0 : ℝ)..pMax,
    finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialXIntegrandZeroBroadeningBoundary
      v m p probeEnergy disorderStrength hbar pMax

/-- Zero-broadening boundary of the finite-cutoff normalized orientation-sensitive transverse
current-rung coefficient. -/
noncomputable def finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficientZeroBroadeningBoundary
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  ∫ p in (0 : ℝ)..pMax,
    finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialYIntegrandZeroBroadeningBoundary
      v m p probeEnergy disorderStrength hbar pMax

private theorem eventually_norm_le_norm_add_one_of_tendsto
    {f : ℝ → ℂ} {z : ℂ}
    (h : Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds z)) :
    ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0), ‖f x‖ ≤ ‖z‖ + 1 := by
  have hclose := (Metric.tendsto_nhds.1 h) 1 zero_lt_one
  filter_upwards [hclose] with x hx
  rw [dist_eq_norm] at hx
  have hdecomp : f x = (f x - z) + z := by abel
  rw [hdecomp]
  calc
    ‖f x - z + z‖ ≤ ‖f x - z‖ + ‖z‖ := norm_add_le _ _
    _ ≤ 1 + ‖z‖ := add_le_add_right hx.le _
    _ = ‖z‖ + 1 := by ring

/-- The finite-broadening longitudinal radial current-rung integrand is strongly measurable in
radial momentum. -/
theorem stronglyMeasurable_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialXIntegrand
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    StronglyMeasurable
      (fun p : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialXIntegrand
          v m p probeEnergy broadening disorderStrength hbar pMax) := by
  apply Measurable.stronglyMeasurable
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialXIntegrand
  simp_rw [finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficient_eq_denominatorForm]
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
    finiteCutoffContinuumBornDysonDenominator
  measurability

/-- The finite-broadening orientation-sensitive radial current-rung integrand is strongly measurable
in radial momentum. -/
theorem stronglyMeasurable_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialYIntegrand
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    StronglyMeasurable
      (fun p : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialYIntegrand
          v m p probeEnergy broadening disorderStrength hbar pMax) := by
  apply Measurable.stronglyMeasurable
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialYIntegrand
  simp_rw [finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficient_eq_denominatorForm]
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
    finiteCutoffContinuumBornDysonDenominator
  measurability

/-- Dominated convergence passes `η → 0⁺` through the normalized longitudinal current-rung radial
integral once a single integrable bound is supplied. -/
theorem tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficient_broadening_zero_of_dominated
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2)
    (hpMax : 0 ≤ pMax)
    (hden : ∀ p ∈ Set.Icc (0 : ℝ) pMax,
      finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary
        v m p probeEnergy disorderStrength hbar pMax ≠ 0)
    (bound : ℝ → ℝ)
    (hBound :
      ∀ᶠ broadening : ℝ in nhdsWithin 0 (Set.Ioi 0),
        ∀ᵐ p ∂(volume.restrict (Set.Icc (0 : ℝ) pMax)),
          ‖finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialXIntegrand
              v m p probeEnergy broadening disorderStrength hbar pMax‖ ≤ bound p)
    (hBoundIntegrable : Integrable bound (volume.restrict (Set.Icc (0 : ℝ) pMax))) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficient
          v m probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficientZeroBroadeningBoundary
          v m probeEnergy disorderStrength hbar pMax)) := by
  have hdom :
      Tendsto
        (fun broadening : ℝ =>
          ∫ p in Set.Icc (0 : ℝ) pMax,
            finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialXIntegrand
              v m p probeEnergy broadening disorderStrength hbar pMax)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (∫ p in Set.Icc (0 : ℝ) pMax,
            finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialXIntegrandZeroBroadeningBoundary
              v m p probeEnergy disorderStrength hbar pMax)) := by
    exact tendsto_integral_filter_of_dominated_convergence
      bound
      (Filter.Eventually.of_forall fun broadening =>
        (stronglyMeasurable_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialXIntegrand
          v m probeEnergy broadening disorderStrength hbar pMax).aestronglyMeasurable)
      hBound hBoundIntegrable
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun p hp =>
        tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialXIntegrand_broadening_zero
          v m p probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff (hden p hp)))
  have hfinite :
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficient
          v m probeEnergy broadening disorderStrength hbar pMax) =
      (fun broadening : ℝ =>
        ∫ p in Set.Icc (0 : ℝ) pMax,
          finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialXIntegrand
            v m p probeEnergy broadening disorderStrength hbar pMax) := by
    funext broadening
    unfold finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficient
    symm
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le hpMax]
  have hboundary :
      finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficientZeroBroadeningBoundary
          v m probeEnergy disorderStrength hbar pMax =
        ∫ p in Set.Icc (0 : ℝ) pMax,
          finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialXIntegrandZeroBroadeningBoundary
            v m p probeEnergy disorderStrength hbar pMax := by
    unfold finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficientZeroBroadeningBoundary
    symm
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le hpMax]
  rw [hfinite, hboundary]
  exact hdom

/-- Dominated convergence passes `η → 0⁺` through the normalized orientation-sensitive current-rung
radial integral once a single integrable bound is supplied. -/
theorem tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficient_broadening_zero_of_dominated
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2)
    (hpMax : 0 ≤ pMax)
    (hden : ∀ p ∈ Set.Icc (0 : ℝ) pMax,
      finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary
        v m p probeEnergy disorderStrength hbar pMax ≠ 0)
    (bound : ℝ → ℝ)
    (hBound :
      ∀ᶠ broadening : ℝ in nhdsWithin 0 (Set.Ioi 0),
        ∀ᵐ p ∂(volume.restrict (Set.Icc (0 : ℝ) pMax)),
          ‖finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialYIntegrand
              v m p probeEnergy broadening disorderStrength hbar pMax‖ ≤ bound p)
    (hBoundIntegrable : Integrable bound (volume.restrict (Set.Icc (0 : ℝ) pMax))) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficient
          v m probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficientZeroBroadeningBoundary
          v m probeEnergy disorderStrength hbar pMax)) := by
  have hdom :
      Tendsto
        (fun broadening : ℝ =>
          ∫ p in Set.Icc (0 : ℝ) pMax,
            finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialYIntegrand
              v m p probeEnergy broadening disorderStrength hbar pMax)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (∫ p in Set.Icc (0 : ℝ) pMax,
            finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialYIntegrandZeroBroadeningBoundary
              v m p probeEnergy disorderStrength hbar pMax)) := by
    exact tendsto_integral_filter_of_dominated_convergence
      bound
      (Filter.Eventually.of_forall fun broadening =>
        (stronglyMeasurable_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialYIntegrand
          v m probeEnergy broadening disorderStrength hbar pMax).aestronglyMeasurable)
      hBound hBoundIntegrable
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun p hp =>
        tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialYIntegrand_broadening_zero
          v m p probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff (hden p hp)))
  have hfinite :
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficient
          v m probeEnergy broadening disorderStrength hbar pMax) =
      (fun broadening : ℝ =>
        ∫ p in Set.Icc (0 : ℝ) pMax,
          finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialYIntegrand
            v m p probeEnergy broadening disorderStrength hbar pMax) := by
    funext broadening
    unfold finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficient
    symm
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le hpMax]
  have hboundary :
      finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficientZeroBroadeningBoundary
          v m probeEnergy disorderStrength hbar pMax =
        ∫ p in Set.Icc (0 : ℝ) pMax,
          finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialYIntegrandZeroBroadeningBoundary
            v m p probeEnergy disorderStrength hbar pMax := by
    unfold finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficientZeroBroadeningBoundary
    symm
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le hpMax]
  rw [hfinite, hboundary]
  exact hdom

/-- A uniform inverse bound for the RA denominator product gives an eventual constant domination of
the normalized longitudinal radial current-rung integrand. -/
theorem eventually_norm_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialXIntegrand_le_of_uniform_inverse_bound
    (v m probeEnergy disorderStrength hbar pMax inverseBound : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2)
    (hpMax : 0 ≤ pMax) (hInverseBoundNonneg : 0 ≤ inverseBound)
    (hInverseBound :
      ∀ᶠ broadening : ℝ in nhdsWithin 0 (Set.Ioi 0),
        ∀ p ∈ Set.Icc (0 : ℝ) pMax,
          ‖(finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
              v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹‖ ≤ inverseBound) :
    ∀ᶠ broadening : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ∀ p ∈ Set.Icc (0 : ℝ) pMax,
        ‖finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialXIntegrand
            v m p probeEnergy broadening disorderStrength hbar pMax‖ ≤
          ‖(((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ))‖ *
            ‖((pMax : ℝ) : ℂ)‖ *
            (‖(((2 * Real.pi : ℝ) : ℂ))‖ * inverseBound *
              (‖finiteCutoffContinuumBornDysonRetardedAdvancedAngularXNumeratorZeroBroadeningBoundary
                  v m probeEnergy disorderStrength hbar pMax‖ + 1)) := by
  have hnum := eventually_norm_le_norm_add_one_of_tendsto
    (tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedAngularXNumerator_broadening_zero
      v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff)
  filter_upwards [hInverseBound, hnum] with broadening hinv hnumAt
  intro p hp
  rw [finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialXIntegrand,
    finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficient_eq_denominatorForm]
  simp only [norm_mul]
  have hpNorm : ‖((p : ℝ) : ℂ)‖ ≤ ‖((pMax : ℝ) : ℂ)‖ := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp.1, abs_of_nonneg hpMax] using hp.2
  gcongr
  · exact hpNorm
  · exact hinv p hp
  · exact hnumAt

/-- A uniform inverse bound for the RA denominator product gives an eventual constant domination of
the normalized orientation-sensitive radial current-rung integrand. -/
theorem eventually_norm_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialYIntegrand_le_of_uniform_inverse_bound
    (v m probeEnergy disorderStrength hbar pMax inverseBound : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2)
    (hpMax : 0 ≤ pMax) (hInverseBoundNonneg : 0 ≤ inverseBound)
    (hInverseBound :
      ∀ᶠ broadening : ℝ in nhdsWithin 0 (Set.Ioi 0),
        ∀ p ∈ Set.Icc (0 : ℝ) pMax,
          ‖(finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
              v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹‖ ≤ inverseBound) :
    ∀ᶠ broadening : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ∀ p ∈ Set.Icc (0 : ℝ) pMax,
        ‖finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialYIntegrand
            v m p probeEnergy broadening disorderStrength hbar pMax‖ ≤
          ‖(((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ))‖ *
            ‖((pMax : ℝ) : ℂ)‖ *
            (‖(((2 * Real.pi : ℝ) : ℂ))‖ * inverseBound *
              (‖finiteCutoffContinuumBornDysonRetardedAdvancedAngularYNumeratorZeroBroadeningBoundary
                  v m probeEnergy disorderStrength hbar pMax‖ + 1)) := by
  have hnum := eventually_norm_le_norm_add_one_of_tendsto
    (tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedAngularYNumerator_broadening_zero
      v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff)
  filter_upwards [hInverseBound, hnum] with broadening hinv hnumAt
  intro p hp
  rw [finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialYIntegrand,
    finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficient_eq_denominatorForm]
  simp only [norm_mul]
  have hpNorm : ‖((p : ℝ) : ℂ)‖ ≤ ‖((pMax : ℝ) : ℂ)‖ := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp.1, abs_of_nonneg hpMax] using hp.2
  gcongr
  · exact hpNorm
  · exact hinv p hp
  · exact hnumAt

/-- The integrated longitudinal current-rung coefficient converges under a compact-radial uniform
inverse bound for the RA denominator product. -/
theorem tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficient_broadening_zero_of_uniform_inverse_bound
    (v m probeEnergy disorderStrength hbar pMax inverseBound : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2)
    (hpMax : 0 ≤ pMax)
    (hden : ∀ p ∈ Set.Icc (0 : ℝ) pMax,
      finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary
        v m p probeEnergy disorderStrength hbar pMax ≠ 0)
    (hInverseBoundNonneg : 0 ≤ inverseBound)
    (hInverseBound :
      ∀ᶠ broadening : ℝ in nhdsWithin 0 (Set.Ioi 0),
        ∀ p ∈ Set.Icc (0 : ℝ) pMax,
          ‖(finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
              v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹‖ ≤ inverseBound) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficient
          v m probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficientZeroBroadeningBoundary
          v m probeEnergy disorderStrength hbar pMax)) := by
  let C : ℝ :=
    ‖(((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ))‖ *
      ‖((pMax : ℝ) : ℂ)‖ *
      (‖(((2 * Real.pi : ℝ) : ℂ))‖ * inverseBound *
        (‖finiteCutoffContinuumBornDysonRetardedAdvancedAngularXNumeratorZeroBroadeningBoundary
            v m probeEnergy disorderStrength hbar pMax‖ + 1))
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  apply tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficient_broadening_zero_of_dominated
    v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff hpMax hden
    (fun _ : ℝ => C)
  · have hbound :=
      eventually_norm_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialXIntegrand_le_of_uniform_inverse_bound
        v m probeEnergy disorderStrength hbar pMax inverseBound hvelocity hmetal hcutoff hpMax
        hInverseBoundNonneg hInverseBound
    filter_upwards [hbound] with broadening hboundAt
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun p hp => hboundAt p hp)
  · refine MeasureTheory.IntegrableOn.of_bound
      isCompact_Icc.measure_lt_top aestronglyMeasurable_const C ?_
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun _ _ => by
      simp [Real.norm_eq_abs, abs_of_nonneg hCnonneg])

/-- The integrated orientation-sensitive current-rung coefficient converges under a compact-radial
uniform inverse bound for the RA denominator product. -/
theorem tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficient_broadening_zero_of_uniform_inverse_bound
    (v m probeEnergy disorderStrength hbar pMax inverseBound : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2)
    (hpMax : 0 ≤ pMax)
    (hden : ∀ p ∈ Set.Icc (0 : ℝ) pMax,
      finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary
        v m p probeEnergy disorderStrength hbar pMax ≠ 0)
    (hInverseBoundNonneg : 0 ≤ inverseBound)
    (hInverseBound :
      ∀ᶠ broadening : ℝ in nhdsWithin 0 (Set.Ioi 0),
        ∀ p ∈ Set.Icc (0 : ℝ) pMax,
          ‖(finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
              v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹‖ ≤ inverseBound) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficient
          v m probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficientZeroBroadeningBoundary
          v m probeEnergy disorderStrength hbar pMax)) := by
  let C : ℝ :=
    ‖(((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ))‖ *
      ‖((pMax : ℝ) : ℂ)‖ *
      (‖(((2 * Real.pi : ℝ) : ℂ))‖ * inverseBound *
        (‖finiteCutoffContinuumBornDysonRetardedAdvancedAngularYNumeratorZeroBroadeningBoundary
            v m probeEnergy disorderStrength hbar pMax‖ + 1))
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  apply tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficient_broadening_zero_of_dominated
    v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff hpMax hden
    (fun _ : ℝ => C)
  · have hbound :=
      eventually_norm_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialYIntegrand_le_of_uniform_inverse_bound
        v m probeEnergy disorderStrength hbar pMax inverseBound hvelocity hmetal hcutoff hpMax
        hInverseBoundNonneg hInverseBound
    filter_upwards [hbound] with broadening hboundAt
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun p hp => hboundAt p hp)
  · refine MeasureTheory.IntegrableOn.of_bound
      isCompact_Icc.measure_lt_top aestronglyMeasurable_const C ?_
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun _ _ => by
      simp [Real.norm_eq_abs, abs_of_nonneg hCnonneg])

end

end QuantumTheory.Transport.Models.MassiveDirac
