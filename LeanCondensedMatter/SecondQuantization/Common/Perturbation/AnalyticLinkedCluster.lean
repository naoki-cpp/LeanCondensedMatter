import LeanCondensedMatter.Analysis.PowerSeries.AnalyticLog
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.AnalyticDysonPartitionFunction

set_option linter.style.header false

/-!
# Analytic finite-configuration linked-cluster bridge

For a finite configuration space, normalize the genuine interacting Dyson partition function by its
free constant term and take the principal complex logarithm near zero coupling. The generic analytic
logarithm theorem identifies its derivatives with the factorial-normalized coefficients of the
formal logarithm of the normalized Dyson trace series.

Particle-specific diagrammatic layers only need to identify those formal-log coefficients with their
connected contributions.

This module is statistics-independent but finite-configuration: the `[Fintype Config]` hypothesis
excludes the full bosonic occupation space even for finitely many bosonic modes. Bosonic analytic
linked-cluster results require a separate convergence-aware interacting Gibbs construction before
they can consume the generic analytic/formal logarithm theorem from `Analysis.PowerSeries`.
-/

namespace SecondQuantization
namespace Common

noncomputable section

variable {Config : Type*} [Fintype Config] [Nonempty Config]

/-- The interacting analytic Dyson partition function normalized by its free constant term. -/
noncomputable def normalizedAnalyticDysonPartitionFunction (energy : Config → ℝ) (β : ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (lam : ℂ) : ℂ :=
  ((PowerSeries.constantCoeff (dysonTraceSeries energy β V))⁻¹ •
    analyticDysonPartitionFunction energy β V) lam

omit [Nonempty Config] in
omit [Nonempty Config] in
private theorem analyticDysonPartitionFunction_zero_eq_constantCoeff
    (energy : Config → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    analyticDysonPartitionFunction energy β V 0 =
      PowerSeries.constantCoeff (dysonTraceSeries energy β V) := by
  rw [analyticDysonPartitionFunction_zero energy hβ V,
    constantCoeff_dysonTraceSeries]
  simpa [weightSum] using
    coe_purePointPartitionFunction_eq_sum_boltzmannWeight energy β

@[simp]
theorem normalizedAnalyticDysonPartitionFunction_zero
    (energy : Config → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    normalizedAnalyticDysonPartitionFunction energy β V 0 = 1 := by
  change (PowerSeries.constantCoeff (dysonTraceSeries energy β V))⁻¹ *
    analyticDysonPartitionFunction energy β V 0 = 1
  rw [analyticDysonPartitionFunction_zero_eq_constantCoeff energy hβ V]
  exact inv_mul_cancel₀ (constantCoeff_dysonTraceSeries_ne_zero energy β V)

omit [Nonempty Config] in
omit [Nonempty Config] in
private theorem hasFPowerSeriesAt_normalizedAnalyticDysonPartitionFunction
    (energy : Config → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    HasFPowerSeriesAt (normalizedAnalyticDysonPartitionFunction energy β V)
      ((PowerSeries.constantCoeff (dysonTraceSeries energy β V))⁻¹ •
        dysonTraceFPowerSeries energy β V) 0 := by
  change HasFPowerSeriesAt
    ((PowerSeries.constantCoeff (dysonTraceSeries energy β V))⁻¹ •
      analyticDysonPartitionFunction energy β V)
    ((PowerSeries.constantCoeff (dysonTraceSeries energy β V))⁻¹ •
      dysonTraceFPowerSeries energy β V) 0
  exact (hasFPowerSeriesAt_analyticDysonPartitionFunction energy hβ V).const_smul

/-- The principal local analytic logarithm of the normalized interacting partition function. -/
noncomputable def analyticNormalizedLogPartitionFunction (energy : Config → ℝ) (β : ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (lam : ℂ) : ℂ :=
  Complex.log (normalizedAnalyticDysonPartitionFunction energy β V lam)

@[simp]
theorem analyticNormalizedLogPartitionFunction_zero
    (energy : Config → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    analyticNormalizedLogPartitionFunction energy β V 0 = 0 := by
  rw [analyticNormalizedLogPartitionFunction,
    normalizedAnalyticDysonPartitionFunction_zero energy hβ V]
  exact Complex.log_one

/-- Derivatives of the normalized analytic log partition function agree with the
factorial-normalized coefficients of the normalized formal Dyson logarithm. -/
theorem iteratedDeriv_analyticNormalizedLogPartitionFunction_eq_factorial_mul_coeff
    (energy : Config → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (n : ℕ) :
    iteratedDeriv n (analyticNormalizedLogPartitionFunction energy β V) 0 =
      (n.factorial : ℂ) *
        PowerSeries.coeff n
          (PowerSeries.logOf
            (PowerSeries.normalizeByConstantCoeff (dysonTraceSeries energy β V))) := by
  unfold analyticNormalizedLogPartitionFunction
  apply PowerSeries.iteratedDeriv_clog_eq_factorial_mul_coeff_logOf
    (hseries := hasFPowerSeriesAt_normalizedAnalyticDysonPartitionFunction energy hβ V)
    (hF0 := normalizedAnalyticDysonPartitionFunction_zero energy hβ V)
    (hcoeff := ?_)
    (hZ := PowerSeries.constantCoeff_normalizeByConstantCoeff
      (constantCoeff_dysonTraceSeries_ne_zero energy β V))
    (n := n)
  intro m
  change (PowerSeries.constantCoeff (dysonTraceSeries energy β V))⁻¹ *
      (dysonTraceFPowerSeries energy β V).coeff m =
    PowerSeries.coeff m
      (PowerSeries.normalizeByConstantCoeff (dysonTraceSeries energy β V))
  rw [coeff_dysonTraceFPowerSeries, PowerSeries.coeff_normalizeByConstantCoeff,
    coeff_dysonTraceSeries]

end
end Common
end SecondQuantization
