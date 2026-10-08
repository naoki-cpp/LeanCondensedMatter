import LeanCondensedMatter.Analysis.PowerSeries.Moment
import LeanCondensedMatter.Analysis.PowerSeries.Normalization
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonTraceSeries

set_option linter.style.header false

/-!
# Statistics-independent finite-configuration Dyson vertex moments

Normalize the Common Dyson trace coefficients by the nonzero free constant term, then package their
factorial-normalized values as a normalized finite-set function. This construction does not use
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

/-- The factorial-normalized Dyson coefficient indexed by an arbitrary finite vertex set. -/
noncomputable def dysonTraceVertexMoment {α : Type*} (energy : Config → ℝ) (β : ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (S : Finset α) : ℂ :=
  (S.card.factorial : ℂ) * normalizedDysonTraceCoeff energy β V S.card

/-- Normalized finite-set moment data of a finite-configuration Dyson trace expansion. -/
noncomputable def dysonTraceVertexMomentSetFunction {α : Type*}
    (energy : Config → ℝ) (β : ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    Combinatorics.NormalizedSetFunction α ℂ where
  toFun := dysonTraceVertexMoment energy β V
  map_empty := by
    simp [dysonTraceVertexMoment]

@[simp]
theorem dysonTraceVertexMomentSetFunction_apply {α : Type*}
    (energy : Config → ℝ) (β : ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (S : Finset α) :
    dysonTraceVertexMomentSetFunction energy β V S =
      dysonTraceVertexMoment energy β V S :=
  rfl

/-- The normalized Dyson trace power-series moments are the Common Dyson vertex moments. -/
theorem powerSeriesMomentSetFunction_normalizeByConstantCoeff_dysonTraceSeries_eq_dysonTraceVertexMomentSetFunction
    {α : Type*} (energy : Config → ℝ) (β : ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hZ : PowerSeries.constantCoeff
      (PowerSeries.normalizeByConstantCoeff (dysonTraceSeries energy β V)) = 1) :
    Combinatorics.powerSeriesMomentSetFunction (α := α)
        (PowerSeries.normalizeByConstantCoeff (dysonTraceSeries energy β V)) hZ =
      dysonTraceVertexMomentSetFunction energy β V := by
  rw [Combinatorics.powerSeriesMomentSetFunction_eq_iff]
  intro S
  simp only [Combinatorics.powerSeriesMomentCoeff,
    dysonTraceVertexMomentSetFunction_apply, dysonTraceVertexMoment,
    PowerSeries.coeff_normalizeByConstantCoeff, coeff_dysonTraceSeries,
    normalizedDysonTraceCoeff, div_eq_mul_inv]
  ac_rfl

end Common
end SecondQuantization
