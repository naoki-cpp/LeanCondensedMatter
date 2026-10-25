import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.FiniteCompatibility
import LeanCondensedMatter.QuantumTheory.Gibbs.Eigenbasis

set_option linter.style.header false

/-!
# Gibbs compatibility between finite and completed configuration Hilbert spaces

For a finite configuration type, the canonical isometry transports Gibbs density
operators and expectations between the finite Hilbert realization and completed
Fock space. These results depend only on the configuration basis, not on
particle statistics or a particular energy function.
-/

namespace SecondQuantization
namespace Common

open QuantumTheory

noncomputable section

variable {Config : Type*} [Fintype Config] [Nonempty Config]

/-- The Gibbs density operators on the completed and finite realizations
intertwine under the canonical isometry, for arbitrary configuration energies. -/
theorem completedFiniteGibbsDensityOperator_intertwines
    (energy : Config → ℝ) (β : ℝ) :
    (completedFiniteHilbertEquiv (Config := Config)).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (eigenbasisGibbsDensityOperator (completedHilbertBasis (Config := Config))
        energy β (eigenbasisGibbsSummable_of_finite energy β)).op =
    (eigenbasisGibbsDensityOperator (finiteHilbertBasis (Config := Config))
      energy β (eigenbasisGibbsSummable_of_finite energy β)).op.comp
        (completedFiniteHilbertEquiv (Config := Config)).toContinuousLinearEquiv.toContinuousLinearMap := by
  have hbasis : ∀ n : Config,
      (completedFiniteHilbertEquiv
        (Config := Config)).toContinuousLinearEquiv.toContinuousLinearMap
          (completedHilbertBasis (Config := Config) n) =
        finiteHilbertBasis (Config := Config) n := by
    intro n
    simpa only [completedHilbertBasis_apply, finiteHilbertBasis_apply,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv] using
      (completedFiniteHilbertEquiv_basisState (Config := Config) n)
  exact eigenbasisGibbsDensityOperator_intertwines
    (completedHilbertBasis (Config := Config))
    (finiteHilbertBasis (Config := Config))
    energy β (eigenbasisGibbsSummable_of_finite energy β)
    (completedFiniteHilbertEquiv (Config := Config)).toContinuousLinearEquiv.toContinuousLinearMap
    hbasis

/-- The finite Gibbs expectation of an algebraic observable equals its
completed Gibbs expectation whenever the completed observable extends the
algebraic one on the finite-support core. -/
theorem finiteGibbsExpectation_eq_completed_of_algebraicCore
    (energy : Config → ℝ) (β : ℝ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (T : CompletedFock Config →L[ℂ] CompletedFock Config)
    (hcore : T.toLinearMap.comp algebraicToCompleted =
      algebraicToCompleted.comp A) :
    (eigenbasisGibbsDensityOperator (finiteHilbertBasis (Config := Config))
      energy β (eigenbasisGibbsSummable_of_finite energy β)).expectation
        (finiteHilbertOperatorAlgEquiv A) =
    (eigenbasisGibbsDensityOperator (completedHilbertBasis (Config := Config))
      energy β (eigenbasisGibbsSummable_of_finite energy β)).expectation T := by
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
