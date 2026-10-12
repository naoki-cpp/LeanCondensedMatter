import LeanCondensedMatter.Analysis.PowerSeries.Normalization
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonTraceSeries

set_option linter.style.header false

/-!
# Statistics-independent finite-configuration Dyson vertex moments

Normalize the Common Dyson trace coefficients by the nonzero free constant term and form
factorial-normalized vertex moments indexed by finite sets. This construction does not use
fermionic statistics; infinite-dimensional bosonic occupation spaces require separate summability
and are not covered by the finite-configuration trace.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*} [Fintype Config] [Nonempty Config]

/-- The n-th Dyson trace coefficient divided by the free partition-function value. -/
noncomputable def normalizedDysonTraceCoeff (energy : Config → ℝ) (β : ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (n : ℕ) : ℂ :=
  dysonTraceCoeff energy β V n /
    PowerSeries.constantCoeff (dysonTraceSeries energy β V)

@[simp]
theorem normalizedDysonTraceCoeff_zero (energy : Config → ℝ) (β : ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    normalizedDysonTraceCoeff energy β V 0 = 1 := by
  have hne := constantCoeff_dysonTraceSeries_ne_zero energy β V
  rw [constantCoeff_dysonTraceSeries] at hne
  simp [normalizedDysonTraceCoeff, dysonTraceCoeff_zero,
    constantCoeff_dysonTraceSeries, hne]

/-- The normalized finite-configuration Dyson coefficient is the free Gibbs expectation of the
bare Dyson coefficient. This identity does not depend on particle statistics. -/
theorem normalizedDysonTraceCoeff_eq_finiteGibbsExpectation (energy : Config → ℝ) (β : ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (n : ℕ) :
    normalizedDysonTraceCoeff energy β V n =
      finiteGibbsExpectation energy β (dysonCoeff energy V n β) := by
  rw [normalizedDysonTraceCoeff, dysonTraceCoeff, constantCoeff_dysonTraceSeries,
    ← traceFock_diagonalEvolution_eq_weightSum]
  exact (finiteGibbsExpectation_eq_trace_div energy β _).symm

/-- The factorial-normalized Dyson coefficient indexed by an arbitrary finite vertex set. -/
noncomputable def dysonTraceVertexMoment {α : Type*} (energy : Config → ℝ) (β : ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (S : Finset α) : ℂ :=
  (S.card.factorial : ℂ) * normalizedDysonTraceCoeff energy β V S.card

end Common
end SecondQuantization
