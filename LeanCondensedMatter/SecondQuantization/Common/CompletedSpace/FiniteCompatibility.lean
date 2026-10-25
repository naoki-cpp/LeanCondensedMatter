import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.Basic
import LeanCondensedMatter.SecondQuantization.Common.Algebra.FiniteHilbertOperator
import Mathlib.Analysis.Normed.Lp.LpEquiv

set_option linter.style.header false

/-!
# Finite-configuration compatibility of completed Fock space

For a finite configuration type, the completed representation `ℓ²(Config, ℂ)` is canonically
linearly isometric to the finite Hilbert realization `EuclideanSpace ℂ Config`.

This construction depends only on the configuration basis, not on particle statistics. It preserves
coordinates, sends the completed basis to the finite Hilbert basis, and intertwines the canonical
algebraic embeddings.
-/

namespace SecondQuantization
namespace Common

noncomputable section

variable {Config : Type*} [Fintype Config]

/-- For finite configuration types, completed Fock space is canonically linearly isometric to the
finite Hilbert realization on the same configurations. -/
noncomputable def completedFiniteHilbertEquiv :
    CompletedFock Config ≃ₗᵢ[ℂ] FiniteHilbertFock Config :=
  lpPiLpₗᵢ (fun _ : Config => ℂ) ℂ

/-- The finite compatibility equivalence intertwines the algebraic-to-completed inclusion with the
algebraic-to-finite-Hilbert equivalence. -/
@[simp]
theorem completedFiniteHilbertEquiv_algebraicToCompleted
    (x : AlgebraicFock Config) :
    completedFiniteHilbertEquiv (Config := Config) (algebraicToCompleted x) =
      finiteHilbertFockEquiv x := by
  ext c
  rfl

/-- The completed configuration basis is exactly the finite Hilbert basis after transport through
the canonical finite compatibility equivalence. -/
@[simp]
theorem completedFiniteHilbertEquiv_basisState (c : Config) :
    completedFiniteHilbertEquiv (Config := Config) (completedBasisState c) =
      finiteHilbertBasisState c := by
  rw [← algebraicToCompleted_basisState,
    completedFiniteHilbertEquiv_algebraicToCompleted]
  exact finiteHilbertFockEquiv_basisState c


/-- A bounded completed operator agreeing with an algebraic endomorphism on the
finite-support core is the finite-Hilbert realization transported back to completed space. -/
theorem completedOperator_eq_transport_of_algebraicCore
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (T : CompletedFock Config →L[ℂ] CompletedFock Config)
    (hcore : T.toLinearMap.comp algebraicToCompleted =
      algebraicToCompleted.comp A) :
    (completedFiniteHilbertEquiv (Config := Config)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((finiteHilbertOperatorAlgEquiv A).comp
        (completedFiniteHilbertEquiv (Config := Config)).toContinuousLinearEquiv.toContinuousLinearMap) = T := by
  let e := completedFiniteHilbertEquiv (Config := Config)
  apply continuousLinearMap_ext_completedBasis
  intro n
  have hn : T (completedBasisState n) =
      algebraicToCompleted (A (basisState n)) := by
    have h := congrArg
      (fun f : AlgebraicFock Config →ₗ[ℂ] CompletedFock Config =>
        f (basisState n)) hcore
    change T (algebraicToCompleted (basisState n)) =
      algebraicToCompleted (A (basisState n)) at h
    rw [algebraicToCompleted_basisState] at h
    exact h
  change e.symm (finiteHilbertOperatorAlgEquiv A
    (e (completedBasisState n))) = T (completedBasisState n)
  rw [completedFiniteHilbertEquiv_basisState,
    finiteHilbertOperator_basisState, hn]
  apply e.injective
  simpa only [e.apply_symm_apply] using
    (completedFiniteHilbertEquiv_algebraicToCompleted
      (A (basisState n))).symm

end
end Common
end SecondQuantization
