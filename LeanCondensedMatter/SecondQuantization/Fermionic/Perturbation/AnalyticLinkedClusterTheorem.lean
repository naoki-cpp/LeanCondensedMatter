import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.AnalyticDysonPartitionFunction
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.LinkedCluster.Theorem
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

set_option linter.style.header false

/-!
# Analytic finite-dimensional fermionic linked-cluster theorem

This module upgrades the algebraic linked-cluster theorem to an analytic statement near zero
coupling. The interacting finite-dimensional partition function is normalized by its free value,
and the principal complex logarithm supplies the local analytic branch through `log 1 = 0`.
-/

open scoped BigOperators Topology

namespace SecondQuantization
namespace Fermionic

open Filter Set

noncomputable section

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The interacting partition function normalized by its free value. -/
noncomputable def normalizedAnalyticDysonPartitionFunction (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (lam : ℂ) : ℂ :=
  ((freePartitionFunction ε β)⁻¹ • analyticDysonPartitionFunction ε β V) lam

omit [LinearOrder Mode] in
@[simp]
theorem normalizedAnalyticDysonPartitionFunction_zero
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    normalizedAnalyticDysonPartitionFunction ε β V 0 = 1 := by
  change (freePartitionFunction ε β)⁻¹ *
    analyticDysonPartitionFunction ε β V 0 = 1
  rw [analyticDysonPartitionFunction_zero ε hβ V]
  exact inv_mul_cancel₀ (freePartitionFunction_ne_zero ε β)

omit [LinearOrder Mode] in
/-- The normalized partition function is analytic at zero coupling. -/
theorem analyticAt_normalizedAnalyticDysonPartitionFunction_zero
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    AnalyticAt ℂ (normalizedAnalyticDysonPartitionFunction ε β V) 0 := by
  change AnalyticAt ℂ
    ((freePartitionFunction ε β)⁻¹ • analyticDysonPartitionFunction ε β V) 0
  exact (analyticAt_analyticDysonPartitionFunction_zero ε hβ V).const_smul

/-- The Taylor series of the normalized partition function, obtained by scaling the Dyson series. -/
noncomputable def normalizedDysonPartitionFPowerSeries (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  (freePartitionFunction ε β)⁻¹ • dysonPartitionFPowerSeries ε β V

omit [LinearOrder Mode] in
/-- The normalized analytic partition function has the scaled Dyson series as its Taylor series. -/
theorem hasFPowerSeriesAt_normalizedAnalyticDysonPartitionFunction
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    HasFPowerSeriesAt (normalizedAnalyticDysonPartitionFunction ε β V)
      (normalizedDysonPartitionFPowerSeries ε β V) 0 := by
  change HasFPowerSeriesAt
    ((freePartitionFunction ε β)⁻¹ • analyticDysonPartitionFunction ε β V)
    ((freePartitionFunction ε β)⁻¹ • dysonPartitionFPowerSeries ε β V) 0
  exact (hasFPowerSeriesAt_analyticDysonPartitionFunction ε hβ V).const_smul

omit [LinearOrder Mode] in
/-- The analytic normalized-series coefficient agrees with the existing formal normalization. -/
theorem coeff_normalizedDysonPartitionFPowerSeries_eq_formal
    (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (n : ℕ) :
    (normalizedDysonPartitionFPowerSeries ε β V).coeff n =
      PowerSeries.coeff n
        (PowerSeries.normalizeByConstantCoeff (dysonPartitionSeries ε β V)) := by
  rw [coeff_normalizeByConstantCoeff_dysonPartitionSeries_eq_normalizedDysonPartitionCoeff,
    normalizedDysonPartitionFPowerSeries, normalizedDysonPartitionCoeff]
  change (freePartitionFunction ε β)⁻¹ *
      (dysonPartitionFPowerSeries ε β V).coeff n =
    dysonPartitionCoeff ε β V n / freePartitionFunction ε β
  rw [coeff_dysonPartitionFPowerSeries, dysonPartitionCoeff_eq_dysonTraceCoeff]
  simp [div_eq_mul_inv, mul_comm]

/-- The local analytic logarithm of the normalized partition function.

The principal complex logarithm is analytic at the base value `1`, so this is the branch selected
near zero coupling. -/
noncomputable def analyticNormalizedLogPartitionFunction (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (lam : ℂ) : ℂ :=
  Complex.log (normalizedAnalyticDysonPartitionFunction ε β V lam)

omit [LinearOrder Mode] in
@[simp]
theorem analyticNormalizedLogPartitionFunction_zero
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    analyticNormalizedLogPartitionFunction ε β V 0 = 0 := by
  rw [analyticNormalizedLogPartitionFunction,
    normalizedAnalyticDysonPartitionFunction_zero ε hβ V]
  exact Complex.log_one

omit [LinearOrder Mode] in
/-- The selected logarithm branch is analytic at zero coupling. -/
theorem analyticAt_analyticNormalizedLogPartitionFunction_zero
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    AnalyticAt ℂ (analyticNormalizedLogPartitionFunction ε β V) 0 := by
  change AnalyticAt ℂ
    (fun z => Complex.log (normalizedAnalyticDysonPartitionFunction ε β V z)) 0
  exact (analyticAt_normalizedAnalyticDysonPartitionFunction_zero ε hβ V).clog
    (by rw [normalizedAnalyticDysonPartitionFunction_zero ε hβ V]; exact Complex.one_mem_slitPlane)

/-- The Taylor series of the principal complex logarithm at `1`. -/
noncomputable def complexLogFPowerSeriesAtOne : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => -(-1 : ℂ) ^ n / n)

/-- The Taylor series obtained by composing the logarithm series with the normalized partition
series. -/
noncomputable def analyticNormalizedLogFPowerSeries (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  complexLogFPowerSeriesAtOne.comp (normalizedDysonPartitionFPowerSeries ε β V)

omit [LinearOrder Mode] in
/-- The local analytic logarithm is represented by the composed Taylor series. -/
theorem hasFPowerSeriesAt_analyticNormalizedLogPartitionFunction
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    HasFPowerSeriesAt (analyticNormalizedLogPartitionFunction ε β V)
      (analyticNormalizedLogFPowerSeries ε β V) 0 := by
  have hlog : HasFPowerSeriesAt Complex.log complexLogFPowerSeriesAtOne
      (normalizedAnalyticDysonPartitionFunction ε β V 0) := by
    rw [normalizedAnalyticDysonPartitionFunction_zero ε hβ V]
    exact hasFPowerSeriesAt_clog_one
  have h := hlog.comp
    (hasFPowerSeriesAt_normalizedAnalyticDysonPartitionFunction ε hβ V)
  change HasFPowerSeriesAt
    (fun x => Complex.log (normalizedAnalyticDysonPartitionFunction ε β V x))
    (complexLogFPowerSeriesAtOne.comp (normalizedDysonPartitionFPowerSeries ε β V)) 0
  exact h

omit [LinearOrder Mode] in
/-- The `n`-th derivative of the analytic logarithm is `n!` times the scalar coefficient of its
composed Taylor series. -/
theorem iteratedDeriv_analyticNormalizedLogPartitionFunction_eq_factorial_mul_coeff
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (n : ℕ) :
    iteratedDeriv n (analyticNormalizedLogPartitionFunction ε β V) 0 =
      (n.factorial : ℂ) * (analyticNormalizedLogFPowerSeries ε β V).coeff n := by
  have hcanonical :=
    (analyticAt_analyticNormalizedLogPartitionFunction_zero ε hβ V).hasFPowerSeriesAt
  have hseries := hasFPowerSeriesAt_analyticNormalizedLogPartitionFunction ε hβ V
  have heq := hcanonical.eq_formalMultilinearSeries hseries
  have hcoeff := congrArg
    (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) heq
  simp only [FormalMultilinearSeries.coeff_ofScalars] at hcoeff
  have hfac : (n.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hmul := (div_eq_iff hfac).mp hcoeff
  simpa [mul_comm] using hmul

end
end Fermionic
end SecondQuantization
