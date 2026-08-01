import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.AnalyticDysonPartitionFunction
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonLinkedClusterTheorem
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

open Filter Set

noncomputable section

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

/-- The interacting partition function normalized by its free value. -/
noncomputable def normalizedAnalyticDysonPartitionFunction (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (lam : ℂ) : ℂ :=
  (freePartitionFunction ε β)⁻¹ * analyticDysonPartitionFunction ε β V lam

omit [LinearOrder Mode] in
@[simp]
theorem normalizedAnalyticDysonPartitionFunction_zero
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    normalizedAnalyticDysonPartitionFunction ε β V 0 = 1 := by
  rw [normalizedAnalyticDysonPartitionFunction,
    analyticDysonPartitionFunction_zero ε hβ V]
  exact inv_mul_cancel₀ (freePartitionFunction_ne_zero ε β)

omit [LinearOrder Mode] in
/-- The normalized partition function is analytic at zero coupling. -/
theorem analyticAt_normalizedAnalyticDysonPartitionFunction_zero
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    AnalyticAt ℂ (normalizedAnalyticDysonPartitionFunction ε β V) 0 := by
  simpa [normalizedAnalyticDysonPartitionFunction, smul_eq_mul] using
    (analyticAt_analyticDysonPartitionFunction_zero ε hβ V).const_smul
      (c := (freePartitionFunction ε β)⁻¹)

/-- The Taylor series of the normalized partition function, obtained by scaling the Dyson series. -/
noncomputable def normalizedDysonPartitionFPowerSeries (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  (freePartitionFunction ε β)⁻¹ • dysonPartitionFPowerSeries ε β V

omit [LinearOrder Mode] in
/-- The normalized analytic partition function has the scaled Dyson series as its Taylor series. -/
theorem hasFPowerSeriesAt_normalizedAnalyticDysonPartitionFunction
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    HasFPowerSeriesAt (normalizedAnalyticDysonPartitionFunction ε β V)
      (normalizedDysonPartitionFPowerSeries ε β V) 0 := by
  simpa [normalizedAnalyticDysonPartitionFunction,
    normalizedDysonPartitionFPowerSeries, smul_eq_mul] using
    (hasFPowerSeriesAt_analyticDysonPartitionFunction ε hβ V).const_smul
      (c := (freePartitionFunction ε β)⁻¹)

omit [LinearOrder Mode] in
/-- The analytic normalized-series coefficient agrees with the existing formal normalization. -/
theorem coeff_normalizedDysonPartitionFPowerSeries_eq_formal
    (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (n : ℕ) :
    (normalizedDysonPartitionFPowerSeries ε β V).coeff n =
      PowerSeries.coeff n (normalizePartitionSeries (dysonPartitionSeries ε β V)) := by
  rw [coeff_normalizePartitionSeries_dysonPartitionSeries_eq_normalizedDysonPartitionCoeff]
  simp [normalizedDysonPartitionFPowerSeries, normalizedDysonPartitionCoeff,
    coeff_dysonPartitionFPowerSeries, dysonPartitionCoeff_eq_dysonTraceCoeff,
    div_eq_mul_inv, mul_comm]

/-- The local analytic logarithm of the normalized partition function.

The principal complex logarithm is analytic at the base value `1`, so this is the branch selected
near zero coupling. -/
noncomputable def analyticNormalizedLogPartitionFunction (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (lam : ℂ) : ℂ :=
  Complex.log (normalizedAnalyticDysonPartitionFunction ε β V lam)

omit [LinearOrder Mode] in
@[simp]
theorem analyticNormalizedLogPartitionFunction_zero
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    analyticNormalizedLogPartitionFunction ε β V 0 = 0 := by
  simp [analyticNormalizedLogPartitionFunction,
    normalizedAnalyticDysonPartitionFunction_zero ε hβ V]

omit [LinearOrder Mode] in
/-- The selected logarithm branch is analytic at zero coupling. -/
theorem analyticAt_analyticNormalizedLogPartitionFunction_zero
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    AnalyticAt ℂ (analyticNormalizedLogPartitionFunction ε β V) 0 := by
  simpa [analyticNormalizedLogPartitionFunction] using
    (analyticAt_normalizedAnalyticDysonPartitionFunction_zero ε hβ V).clog
      (by simp [normalizedAnalyticDysonPartitionFunction_zero ε hβ V])

/-- The Taylor series of the principal complex logarithm at `1`. -/
noncomputable def complexLogFPowerSeriesAtOne : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => -(-1 : ℂ) ^ n / n)

/-- The Taylor series obtained by composing the logarithm series with the normalized partition
series. -/
noncomputable def analyticNormalizedLogFPowerSeries (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  complexLogFPowerSeriesAtOne.comp (normalizedDysonPartitionFPowerSeries ε β V)

omit [LinearOrder Mode] in
/-- The local analytic logarithm is represented by the composed Taylor series. -/
theorem hasFPowerSeriesAt_analyticNormalizedLogPartitionFunction
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    HasFPowerSeriesAt (analyticNormalizedLogPartitionFunction ε β V)
      (analyticNormalizedLogFPowerSeries ε β V) 0 := by
  have h := Complex.hasFPowerSeriesAt_clog_one.comp
    (hasFPowerSeriesAt_normalizedAnalyticDysonPartitionFunction ε hβ V)
  simpa [analyticNormalizedLogPartitionFunction, analyticNormalizedLogFPowerSeries,
    complexLogFPowerSeriesAtOne, Function.comp_def] using h

omit [LinearOrder Mode] in
/-- The `n`-th derivative of the analytic logarithm is `n!` times the scalar coefficient of its
composed Taylor series. -/
theorem iteratedDeriv_analyticNormalizedLogPartitionFunction_eq_factorial_mul_coeff
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (n : ℕ) :
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
end SecondQuantization
