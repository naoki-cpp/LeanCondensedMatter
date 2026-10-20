import LeanCondensedMatter.Analysis.PowerSeries.Moment
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonTraceSeries

set_option linter.style.header false

/-!
# Finite-configuration Dyson trace moment realization

The factorial-normalized Dyson vertex moments are the generic
`Combinatorics.powerSeriesMomentCoeff` of the normalized Dyson trace series;
no Dyson-specific coefficient or finite-set moment definitions are needed.

This module retains only the statistics-independent bridge from those generic
normalized series coefficients to the finite Gibbs expectation of each Dyson
coefficient. The finite-configuration trace requires `[Fintype Config]`;
infinite bosonic occupation spaces need their own summability hypotheses.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*} [Fintype Config] [Nonempty Config]

/-- The normalized Dyson-series coefficient is the finite Gibbs expectation of the
bare Dyson coefficient, independently of particle statistics. -/
theorem coeff_normalizeByConstantCoeff_dysonTraceSeries_eq_finiteGibbsExpectation
    (energy : Config → ℝ) (β : ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (n : ℕ) :
    PowerSeries.coeff n
        (PowerSeries.normalizeByConstantCoeff (dysonTraceSeries energy β V)) =
      finiteGibbsExpectation energy β (dysonCoeff energy V n β) := by
  rw [PowerSeries.coeff_normalizeByConstantCoeff,
    coeff_dysonTraceSeries, dysonTraceCoeff,
    constantCoeff_dysonTraceSeries,
    ← traceFock_diagonalEvolution_eq_weightSum]
  simpa only [div_eq_mul_inv, mul_comm] using
    (finiteGibbsExpectation_eq_trace_div energy β _).symm

end Common
end SecondQuantization
