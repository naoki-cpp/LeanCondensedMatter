import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonExpansion
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.GibbsExpectation.Core
import Mathlib.RingTheory.PowerSeries.Basic

set_option linter.style.header false

/-!
# Finite-configuration Dyson trace series

For a finite configuration type, a basis-diagonal free energy, and an arbitrary interaction
operator, this file packages the algebraic Dyson coefficients into the statistics-independent
trace coefficients

`Tr[diagonalEvolution energy (-β) ∘ Dₙ(β)]`

and the corresponding formal power series. The trace can equivalently be written as the finite
Boltzmann-weighted diagonal functional of `Dₙ(β)`. No convergence or identification with an
analytic partition function is asserted here.
-/

namespace SecondQuantization
namespace Common

open PowerSeries

variable {Config : Type*} [Fintype Config]

/-- The `n`-th finite Dyson trace coefficient,
`Tr[diagonalEvolution energy (-β) ∘ Dₙ(β)]`. -/
noncomputable def dysonTraceCoeff (energy : Config → ℝ) (β : ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (n : ℕ) : ℂ :=
  traceFock ((diagonalEvolution energy (-β)).comp (dysonCoeff energy V n β))

/-- A Dyson trace coefficient is the Boltzmann-weighted trace of the corresponding bare Dyson
coefficient. -/
theorem dysonTraceCoeff_eq_weightedTrace (energy : Config → ℝ) (β : ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (n : ℕ) :
    dysonTraceCoeff energy β V n =
      weightedTrace (boltzmannWeight energy β) (dysonCoeff energy V n β) :=
  traceFock_diagonalEvolution_comp_eq_weightedTrace energy β (dysonCoeff energy V n β)

/-- The formal power series whose coefficients are the finite Dyson trace coefficients. -/
noncomputable def dysonTraceSeries (energy : Config → ℝ) (β : ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) : PowerSeries ℂ :=
  PowerSeries.mk (dysonTraceCoeff energy β V)

theorem coeff_dysonTraceSeries (energy : Config → ℝ) (β : ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (n : ℕ) :
    PowerSeries.coeff n (dysonTraceSeries energy β V) = dysonTraceCoeff energy β V n :=
  PowerSeries.coeff_mk n _

/-- The zeroth Dyson trace coefficient is the finite free weight sum. -/
@[simp]
theorem dysonTraceCoeff_zero (energy : Config → ℝ) (β : ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    dysonTraceCoeff energy β V 0 = weightSum (boltzmannWeight energy β) := by
  rw [dysonTraceCoeff, dysonCoeff_zero, LinearMap.comp_id,
    traceFock_diagonalEvolution_eq_weightSum]

/-- The constant coefficient of the finite Dyson trace series is the finite free weight sum. -/
theorem constantCoeff_dysonTraceSeries (energy : Config → ℝ) (β : ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    PowerSeries.constantCoeff (dysonTraceSeries energy β V) =
      weightSum (boltzmannWeight energy β) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_dysonTraceSeries, dysonTraceCoeff_zero]

variable [Nonempty Config]

/-- The normalized finite Dyson coefficient evaluated in the canonical Gibbs density state. -/
noncomputable def normalizedDysonTraceCoeff (energy : Config → ℝ) (β : ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (n : ℕ) : ℂ :=
  finiteGibbsExpectation energy β (dysonCoeff energy V n β)

/-- The normalized zeroth Dyson coefficient is one by density-state normalization. -/
@[simp]
theorem normalizedDysonTraceCoeff_zero (energy : Config → ℝ) (β : ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    normalizedDysonTraceCoeff energy β V 0 = 1 := by
  simpa only [normalizedDysonTraceCoeff, dysonCoeff_zero] using finiteGibbsExpectation_id energy β

end Common
end SecondQuantization
