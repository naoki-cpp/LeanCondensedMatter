import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.FockSpace
import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.Basic

set_option linter.style.header false

/-!
# Completed bosonic Fock space

The completed bosonic occupation representation is the generic completed Fock space specialized to
bosonic occupation configurations:

`ℓ²(Bosonic.Occupation Mode, ℂ)`.

Only the canonical completed basis and the dense algebraic inclusion are exposed here. Bosonic
creation and annihilation operators remain unbounded in this representation and are therefore not
packaged as continuous linear maps.
-/

namespace SecondQuantization
namespace Bosonic

noncomputable section

/-- The completed bosonic Fock space. -/
abbrev CompletedFockSpace (Mode : Type*) :=
  Common.CompletedFock (Occupation Mode)

variable {Mode : Type*}

/-- The canonical occupation-basis vector in completed bosonic Fock space. -/
noncomputable def completedBasisState (n : Occupation Mode) : CompletedFockSpace Mode :=
  Common.completedBasisState n

/-- The canonical occupation Hilbert basis of completed bosonic Fock space. -/
noncomputable def completedOccupationHilbertBasis :
    HilbertBasis (Occupation Mode) ℂ (CompletedFockSpace Mode) :=
  Common.completedHilbertBasis

@[simp]
theorem completedOccupationHilbertBasis_apply (n : Occupation Mode) :
    completedOccupationHilbertBasis (Mode := Mode) n = completedBasisState n := by
  simpa [completedOccupationHilbertBasis, completedBasisState] using
    (Common.completedHilbertBasis_apply (Config := Occupation Mode) n)

@[simp]
theorem completedBasisState_apply_self (n : Occupation Mode) :
    completedBasisState n n = 1 := by
  simpa [completedBasisState] using
    (Common.completedBasisState_apply_self (Config := Occupation Mode) n)

@[simp]
theorem completedBasisState_apply_of_ne {m n : Occupation Mode} (h : m ≠ n) :
    completedBasisState n m = 0 := by
  simpa [completedBasisState] using
    (Common.completedBasisState_apply_of_ne (Config := Occupation Mode) h)

/-- The coordinate-preserving inclusion of algebraic bosonic Fock space into its `ℓ²` completion. -/
noncomputable def algebraicToCompleted :
    FockSpace Mode →ₗ[ℂ] CompletedFockSpace Mode :=
  Common.algebraicToCompleted

@[simp]
theorem algebraicToCompleted_basisState (n : Occupation Mode) :
    algebraicToCompleted (basisState n) = completedBasisState n := by
  change Common.algebraicToCompleted (Common.basisState n) = Common.completedBasisState n
  exact Common.algebraicToCompleted_basisState n

end
end Bosonic
end SecondQuantization
