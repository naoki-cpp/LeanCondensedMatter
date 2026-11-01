import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.FiniteCompatibility
import LeanCondensedMatter.SecondQuantization.Common.Thermal.GibbsExpectation
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsExpectationBridge

set_option linter.style.header false

/-!
# Gibbs compatibility between finite and completed configuration Hilbert spaces

For a finite configuration type, the canonical isometry identifies the algebraic
finite Gibbs expectation with the summability-aware completed Gibbs functional.
The result is independent of particle statistics and the energy function.
-/

namespace SecondQuantization
namespace Common

open QuantumTheory

noncomputable section

variable {Config : Type*} [Fintype Config] [Nonempty Config]

/-- The finite Gibbs expectation of an algebraic observable equals its
completed Gibbs expectation whenever the completed observable extends the
algebraic one on the finite-support core. -/
theorem finiteGibbsExpectation_eq_completed_of_algebraicCore
    (energy : Config → ℝ) (β : ℝ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (T : CompletedFock Config →L[ℂ] CompletedFock Config)
    (hcore : T.toLinearMap.comp algebraicToCompleted =
      algebraicToCompleted.comp A) :
    finiteGibbsExpectation energy β A =
      gibbsExpectation energy β (eigenbasisGibbsSummable_of_finite energy β) T := by
  change
    (eigenbasisGibbsDensityOperator (finiteHilbertBasis (Config := Config))
      energy β (eigenbasisGibbsSummable_of_finite energy β)).expectation
        (finiteHilbertOperatorAlgEquiv A) =
    (eigenbasisGibbsDensityOperator (completedHilbertBasis (Config := Config))
      energy β (eigenbasisGibbsSummable_of_finite energy β)).expectation T
  let e := completedFiniteHilbertEquiv (Config := Config)
  have hbasis : ∀ n : Config,
      e (completedHilbertBasis (Config := Config) n) =
        finiteHilbertBasis (Config := Config) n := by
    intro n
    simpa only [completedHilbertBasis_apply, finiteHilbertBasis_apply] using
      (completedFiniteHilbertEquiv_basisState (Config := Config) n)
  have htransport :=
    eigenbasisGibbsDensityOperator_expectation_transport
      (completedHilbertBasis (Config := Config))
      (finiteHilbertBasis (Config := Config))
      energy β (eigenbasisGibbsSummable_of_finite energy β) e hbasis
      (finiteHilbertOperatorAlgEquiv A)
  rw [completedOperator_eq_transport_of_algebraicCore A T hcore] at htransport
  exact htransport

end
end Common
end SecondQuantization
