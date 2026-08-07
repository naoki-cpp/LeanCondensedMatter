import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.FiniteCompatibility
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Core

set_option linter.style.header false

/-!
# Finite-mode compatibility of bounded completed fermionic operators

The finite-mode isometry from `FiniteCompatibility.lean` should not merely identify vectors: it
must identify the bounded operator realizations already present on the completed and finite Hilbert
spaces.

The main theorem below is deliberately generic.  Whenever a completed bounded operator agrees with
an algebraic Fock endomorphism on the dense algebraic core, transport through
`completedFiniteHilbertEquiv` agrees with the existing `Common.finiteHilbertOperator` construction.
The completed number, creation, and annihilation operators then follow immediately from their
existing core-agreement theorems.
-/

namespace SecondQuantization
namespace Fermionic

noncomputable section

variable {Mode : Type*} [Fintype Mode]

/-- Continuous-linear form of the canonical finite-mode Hilbert-space equivalence. -/
noncomputable def completedFiniteHilbertContinuousEquiv :
    CompletedFockSpace Mode ≃L[ℂ] Common.FiniteHilbertFock (Occupation Mode) :=
  (completedFiniteHilbertEquiv (Mode := Mode)).toContinuousLinearEquiv

@[simp]
theorem completedFiniteHilbertContinuousEquiv_apply (ψ : CompletedFockSpace Mode) :
    completedFiniteHilbertContinuousEquiv (Mode := Mode) ψ =
      completedFiniteHilbertEquiv (Mode := Mode) ψ :=
  rfl

omit [Fintype Mode] in
private theorem continuousLinearMap_ext_algebraicCore_to_finite
    {A B : CompletedFockSpace Mode →L[ℂ] Common.FiniteHilbertFock (Occupation Mode)}
    (h : ∀ x : FockSpace Mode, A (algebraicToCompleted x) = B (algebraicToCompleted x)) :
    A = B := by
  apply DFunLike.ext'
  exact (map_continuous A).ext_on algebraicToCompleted_denseRange (map_continuous B) <| by
    rintro _ ⟨x, rfl⟩
    exact h x

/-- Any bounded completed operator that agrees with an algebraic Fock endomorphism on the canonical
core becomes the existing finite-Hilbert transport of that algebraic operator after applying the
finite-mode compatibility equivalence. -/
theorem completedFiniteHilbertEquiv_intertwines_of_core
    (A : FockSpace Mode →ₗ[ℂ] FockSpace Mode)
    (Ahat : CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode)
    (hcore : Ahat.toLinearMap.comp algebraicToCompleted =
      algebraicToCompleted.comp A) :
    (completedFiniteHilbertContinuousEquiv (Mode := Mode)).toContinuousLinearMap.comp Ahat =
      (Common.finiteHilbertOperator A).comp
        (completedFiniteHilbertContinuousEquiv (Mode := Mode)).toContinuousLinearMap := by
  apply continuousLinearMap_ext_algebraicCore_to_finite
  intro x
  have hx := congrArg (fun f : FockSpace Mode →ₗ[ℂ] CompletedFockSpace Mode => f x) hcore
  simp only [LinearMap.comp_apply] at hx
  simp only [ContinuousLinearMap.comp_apply]
  change completedFiniteHilbertEquiv (Mode := Mode) (Ahat (algebraicToCompleted x)) =
    Common.finiteHilbertOperator A
      (completedFiniteHilbertEquiv (Mode := Mode) (algebraicToCompleted x))
  rw [hx, completedFiniteHilbertEquiv_algebraicToCompleted,
    completedFiniteHilbertEquiv_algebraicToCompleted,
    Common.finiteHilbertOperator_equiv_apply]

variable [LinearOrder Mode]

/-- The completed single-mode number projection transports to the existing finite-Hilbert number
operator. -/
theorem completedFiniteHilbertEquiv_intertwines_numberOperator (i : Mode) :
    (completedFiniteHilbertContinuousEquiv (Mode := Mode)).toContinuousLinearMap.comp
        (completedNumberOperator i) =
      (Common.finiteHilbertOperator (numberOperator i)).comp
        (completedFiniteHilbertContinuousEquiv (Mode := Mode)).toContinuousLinearMap := by
  exact completedFiniteHilbertEquiv_intertwines_of_core (numberOperator i)
    (completedNumberOperator i) (completedNumberOperator_comp_algebraicToCompleted i)

/-- Completed fermionic creation transports to the existing finite-Hilbert transport of algebraic
creation. -/
theorem completedFiniteHilbertEquiv_intertwines_create (i : Mode) :
    (completedFiniteHilbertContinuousEquiv (Mode := Mode)).toContinuousLinearMap.comp
        (completedCreate i) =
      (Common.finiteHilbertOperator (create i)).comp
        (completedFiniteHilbertContinuousEquiv (Mode := Mode)).toContinuousLinearMap := by
  exact completedFiniteHilbertEquiv_intertwines_of_core (create i)
    (completedCreate i) (completedCreate_comp_algebraicToCompleted i)

/-- Completed fermionic annihilation transports to the existing finite-Hilbert transport of
algebraic annihilation. -/
theorem completedFiniteHilbertEquiv_intertwines_annihilate (i : Mode) :
    (completedFiniteHilbertContinuousEquiv (Mode := Mode)).toContinuousLinearMap.comp
        (completedAnnihilate i) =
      (Common.finiteHilbertOperator (annihilate i)).comp
        (completedFiniteHilbertContinuousEquiv (Mode := Mode)).toContinuousLinearMap := by
  exact completedFiniteHilbertEquiv_intertwines_of_core (annihilate i)
    (completedAnnihilate i) (completedAnnihilate_comp_algebraicToCompleted i)

end
end Fermionic
end SecondQuantization
