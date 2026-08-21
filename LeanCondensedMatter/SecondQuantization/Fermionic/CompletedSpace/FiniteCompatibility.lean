import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Basic
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteHilbertOperator
import Mathlib.Analysis.Normed.Lp.LpEquiv

set_option linter.style.header false

/-!
# Finite-mode compatibility of the completed fermionic Fock space

For a finite mode type, the completed occupation representation

```text
ℓ²(Occupation Mode, ℂ)
```

is finite dimensional.  The common finite Hilbert API realizes the same occupation coordinates as
`Common.FiniteHilbertFock (Occupation Mode) = EuclideanSpace ℂ (Occupation Mode)`.

This file identifies the two Hilbert realizations by Mathlib's canonical finite-index
`lp`–`PiLp` linear isometry equivalence.  The map preserves occupation coordinates, sends the
completed occupation basis to the finite Hilbert basis, and makes the algebraic Fock core commute
with `Common.finiteHilbertFockEquiv`.
-/

namespace SecondQuantization
namespace Fermionic

noncomputable section

variable {Mode : Type*} [Fintype Mode]

/-- For finite mode sets, completed fermionic Fock space is canonically isometrically equivalent to
the finite Hilbert Fock realization on the same occupation configurations. -/
noncomputable def completedFiniteHilbertEquiv :
    CompletedFockSpace Mode ≃ₗᵢ[ℂ] Common.FiniteHilbertFock (Occupation Mode) :=
  lpPiLpₗᵢ (fun _ : Occupation Mode => ℂ) ℂ

/-- Continuous-linear form of the canonical finite-mode Hilbert-space equivalence. -/
noncomputable def completedFiniteHilbertContinuousEquiv :
    CompletedFockSpace Mode ≃L[ℂ] Common.FiniteHilbertFock (Occupation Mode) :=
  (completedFiniteHilbertEquiv (Mode := Mode)).toContinuousLinearEquiv

/-- The finite compatibility equivalence intertwines the algebraic-to-completed inclusion with the
algebraic-to-finite-Hilbert equivalence. -/
@[simp]
theorem completedFiniteHilbertEquiv_algebraicToCompleted
    (x : OccupationFock Mode) :
    completedFiniteHilbertEquiv (Mode := Mode) (algebraicToCompleted x) =
      Common.finiteHilbertFockEquiv x := by
  ext n
  rfl

/-- The completed occupation basis is exactly the finite Hilbert occupation basis after transport
through the canonical finite compatibility equivalence. -/
@[simp]
theorem completedFiniteHilbertEquiv_basisState (n : Occupation Mode) :
    completedFiniteHilbertEquiv (Mode := Mode) (completedBasisState n) =
      Common.finiteHilbertBasisState n := by
  rw [← algebraicToCompleted_basisState,
    completedFiniteHilbertEquiv_algebraicToCompleted]
  change Common.finiteHilbertFockEquiv (Common.basisState n) =
    Common.finiteHilbertBasisState n
  exact Common.finiteHilbertFockEquiv_basisState n

omit [Fintype Mode] in
/-- It suffices to compare two continuous maps on the completed occupation basis. -/
theorem continuousLinearMap_ext_completedBasis_to_finite
    {A B : CompletedFockSpace Mode →L[ℂ] Common.FiniteHilbertFock (Occupation Mode)}
    (h : ∀ n : Occupation Mode, A (completedBasisState n) = B (completedBasisState n)) :
    A = B := by
  apply DFunLike.ext'
  exact (map_continuous A).ext_on algebraicToCompleted_denseRange (map_continuous B) <| by
    rintro _ ⟨x, rfl⟩
    have hmaps : A.toLinearMap.comp algebraicToCompleted =
        B.toLinearMap.comp algebraicToCompleted := by
      apply Finsupp.lhom_ext
      intro n c
      have hc : (Finsupp.single n c : OccupationFock Mode) = c • basisState n :=
        (Finsupp.smul_single_one n c).symm
      rw [hc]
      simp only [LinearMap.comp_apply, map_smul, algebraicToCompleted_basisState]
      exact congrArg (fun y : Common.FiniteHilbertFock (Occupation Mode) => c • y) (h n)
    exact congrArg (fun f : OccupationFock Mode →ₗ[ℂ]
      Common.FiniteHilbertFock (Occupation Mode) => f x) hmaps

end
end Fermionic
end SecondQuantization
