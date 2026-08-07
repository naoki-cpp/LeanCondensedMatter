import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.FreeGibbsSummability
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsDensityOperator
import Mathlib.Analysis.Normed.Lp.LpEquiv

set_option linter.style.header false

/-!
# Finite-mode compatibility of the completed fermionic Fock space

For a finite mode type, the completed occupation representation

```text
ℓ²(Occupation Mode, ℂ)
```

is finite dimensional.  The existing finite thermal API realizes the same occupation coordinates as
`Common.FiniteHilbertFock (Occupation Mode) = EuclideanSpace ℂ (Occupation Mode)`.

This file identifies the two Hilbert realizations by Mathlib's canonical finite-index
`lp`–`PiLp` linear isometry equivalence.  The map preserves occupation coordinates, sends the
completed occupation basis to the existing finite Hilbert basis, and makes the algebraic Fock core
commute with the existing `Common.finiteHilbertFockEquiv`.
-/

namespace SecondQuantization
namespace Fermionic

noncomputable section

variable {Mode : Type*} [Fintype Mode]

/-- For finite mode sets, completed fermionic Fock space is canonically isometrically equivalent to
the existing finite Hilbert Fock realization on the same occupation configurations. -/
noncomputable def completedFiniteHilbertEquiv :
    CompletedFockSpace Mode ≃ₗᵢ[ℂ] Common.FiniteHilbertFock (Occupation Mode) :=
  lpPiLpₗᵢ (fun _ : Occupation Mode => ℂ) ℂ

/-- The finite compatibility equivalence preserves every occupation coordinate. -/
@[simp]
theorem completedFiniteHilbertEquiv_apply
    (ψ : CompletedFockSpace Mode) (n : Occupation Mode) :
    completedFiniteHilbertEquiv (Mode := Mode) ψ n = ψ n := by
  rfl

/-- The finite compatibility equivalence intertwines the algebraic-to-completed inclusion with the
existing algebraic-to-finite-Hilbert equivalence. -/
@[simp]
theorem completedFiniteHilbertEquiv_algebraicToCompleted
    (x : FockSpace Mode) :
    completedFiniteHilbertEquiv (Mode := Mode) (algebraicToCompleted x) =
      Common.finiteHilbertFockEquiv x := by
  ext n
  rfl

/-- The completed occupation basis is exactly the existing finite Hilbert occupation basis after
transport through the canonical finite compatibility equivalence. -/
@[simp]
theorem completedFiniteHilbertEquiv_basisState (n : Occupation Mode) :
    completedFiniteHilbertEquiv (Mode := Mode) (completedBasisState n) =
      Common.finiteHilbertBasisState n := by
  rw [← algebraicToCompleted_basisState,
    completedFiniteHilbertEquiv_algebraicToCompleted]
  change Common.finiteHilbertFockEquiv (Common.basisState n) =
    Common.finiteHilbertBasisState n
  exact Common.finiteHilbertFockEquiv_basisState n

/-- Linear-map form of the finite compatibility square on the full algebraic Fock core. -/
theorem completedFiniteHilbertEquiv_comp_algebraicToCompleted :
    (completedFiniteHilbertEquiv (Mode := Mode)).toLinearMap.comp algebraicToCompleted =
      (Common.finiteHilbertFockEquiv (Config := Occupation Mode)).toLinearMap := by
  apply LinearMap.ext
  intro x
  exact completedFiniteHilbertEquiv_algebraicToCompleted x

end
end Fermionic
end SecondQuantization
