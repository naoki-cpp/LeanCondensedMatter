import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.Basic
import LeanCondensedMatter.QuantumTheory.Gibbs.Eigenbasis

set_option linter.style.header false

/-!
# Summability-aware Gibbs expectation on completed configuration space

The normalized Gibbs expectation of a bounded completed-Fock observable is
defined for any configuration type carrying summable Boltzmann weights.
No finiteness assumption or particle statistics is needed; finite algebraic
operators are connected through the separate finite/completed compatibility
theorem. The underlying state remains the generic pure-point Gibbs density.
-/

namespace SecondQuantization
namespace Common

open QuantumTheory

noncomputable section

variable {Config : Type*} [Nonempty Config]

/-- The pure-point Gibbs expectation of a bounded completed-Fock operator.
Boltzmann summability is explicit; unlike the finite algebraic implementation,
this does not assume `Fintype Config`. -/
noncomputable def gibbsExpectation
    (energy : Config → ℝ) (β : ℝ)
    (hsum : EigenbasisGibbsSummable energy β) :
    (CompletedFock Config →L[ℂ] CompletedFock Config) →L[ℂ] ℂ :=
  (eigenbasisGibbsDensityOperator
    (completedHilbertBasis (Config := Config)) energy β hsum).expectation

/-- Gibbs expectations are normalized, also for infinite configuration types. -/
@[simp]
theorem gibbsExpectation_id
    (energy : Config → ℝ) (β : ℝ)
    (hsum : EigenbasisGibbsSummable energy β) :
    gibbsExpectation energy β hsum
      (ContinuousLinearMap.id ℂ (CompletedFock Config)) = 1 := by
  exact (eigenbasisGibbsDensityOperator
    (completedHilbertBasis (Config := Config)) energy β hsum).expectation_id

/-- The completed Gibbs expectation is the summable normalized diagonal series.
Finite sums are a specialization of this representation. -/
theorem gibbsExpectation_eq_tsum
    (energy : Config → ℝ) (β : ℝ)
    (hsum : EigenbasisGibbsSummable energy β)
    (A : CompletedFock Config →L[ℂ] CompletedFock Config) :
    gibbsExpectation energy β hsum A =
      ∑' c : Config, (eigenbasisGibbsProbability energy β c : ℂ) *
        inner ℂ (completedBasisState c) (A (completedBasisState c)) := by
  change (eigenbasisGibbsDensityOperator
    (completedHilbertBasis (Config := Config)) energy β hsum).expectation A = _
  rw [(eigenbasisGibbsDensityOperator
    (completedHilbertBasis (Config := Config)) energy β hsum).expectation_eq_tsum_diagonal
      A (completedHilbertBasis (Config := Config))
      (eigenbasisGibbsProbability energy β)
      (eigenbasisGibbsDensityOperator_apply_basis
        (completedHilbertBasis (Config := Config)) energy β hsum)]
  simp only [completedHilbertBasis_apply]

end
end Common
end SecondQuantization
