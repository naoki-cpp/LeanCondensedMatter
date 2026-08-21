import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.NumberOperator
import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.CoordinateProjection

set_option linter.style.header false

/-!
# Completed fermionic Fock space

This file specializes the statistics-independent completed Fock infrastructure in
`Common.CompletedSpace.Basic` to fermionic occupation configurations. The completed fermionic Fock
space is `ℓ²(Fermionic.Occupation Mode, ℂ)`.

The generic Hilbert-space construction, canonical basis, dense algebraic inclusion, and coordinate
projection backend are owned by `Common`. This file keeps readable fermionic specialization names
together with the genuinely fermionic single-mode occupation predicate.
-/

namespace SecondQuantization
namespace Fermionic

open scoped ENNReal

noncomputable section

/-- The completed fermionic Fock space: the generic completed Fock space on fermionic occupations. -/
abbrev CompletedFockSpace (Mode : Type*) :=
  Common.CompletedFock (Occupation Mode)

variable {Mode : Type*}

/-- The canonical occupation-basis vector in completed fermionic Fock space. -/
noncomputable def completedBasisState (n : Occupation Mode) : CompletedFockSpace Mode :=
  Common.completedBasisState n

/-- The canonical occupation Hilbert basis of completed fermionic Fock space. -/
noncomputable def completedOccupationHilbertBasis :
    HilbertBasis (Occupation Mode) ℂ (CompletedFockSpace Mode) :=
  Common.completedHilbertBasis

@[simp]
theorem completedOccupationHilbertBasis_apply (n : Occupation Mode) :
    completedOccupationHilbertBasis (Mode := Mode) n = completedBasisState n := by
  simpa [completedOccupationHilbertBasis, completedBasisState] using
    (Common.completedHilbertBasis_apply (Config := Occupation Mode) n)

/-- Inner product with a completed occupation basis vector in the first slot evaluates the
corresponding coordinate. -/
@[simp]
theorem inner_completedBasisState_left (n : Occupation Mode) (ψ : CompletedFockSpace Mode) :
    inner ℂ (completedBasisState n) ψ = ψ n := by
  simpa [completedBasisState] using
    (Common.inner_completedBasisState_left (Config := Occupation Mode) n ψ)

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

/-- The coordinate-preserving inclusion of algebraic fermionic Fock space into its `ℓ²` completion. -/
noncomputable def algebraicToCompleted :
    OccupationFock Mode →ₗ[ℂ] CompletedFockSpace Mode :=
  Common.algebraicToCompleted

@[simp]
theorem algebraicToCompleted_apply (x : OccupationFock Mode) (n : Occupation Mode) :
    algebraicToCompleted x n = x n :=
  rfl

@[simp]
theorem algebraicToCompleted_basisState (n : Occupation Mode) :
    algebraicToCompleted (basisState n) = completedBasisState n := by
  simpa [algebraicToCompleted, basisState, completedBasisState] using
    (Common.algebraicToCompleted_basisState (Config := Occupation Mode) n)

/-- The algebraic-to-completed inclusion loses no finite-support vector. -/
theorem algebraicToCompleted_injective :
    Function.Injective
      (algebraicToCompleted : OccupationFock Mode → CompletedFockSpace Mode) := by
  simpa [algebraicToCompleted] using
    (Common.algebraicToCompleted_injective (Config := Occupation Mode))

/-- Finite-support fermionic Fock vectors are dense in the completed `ℓ²` space. -/
theorem algebraicToCompleted_denseRange :
    DenseRange
      (algebraicToCompleted : OccupationFock Mode → CompletedFockSpace Mode) := by
  simpa [algebraicToCompleted] using
    (Common.algebraicToCompleted_denseRange (Config := Occupation Mode))

variable [LinearOrder Mode]

/-- The completed single-mode number operator. It is the orthogonal coordinate projection onto
occupation configurations containing `i`, hence has operator norm at most one. -/
noncomputable def completedNumberOperator (i : Mode) :
    CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode :=
  Common.completedCoordinateProjection (fun n : Occupation Mode => i ∈ n)

@[simp]
theorem completedNumberOperator_apply (i : Mode) (ψ : CompletedFockSpace Mode)
    (n : Occupation Mode) :
    completedNumberOperator i ψ n = if i ∈ n then ψ n else 0 := by
  simpa [completedNumberOperator] using
    (Common.completedCoordinateProjection_apply
      (Config := Occupation Mode) (fun m : Occupation Mode => i ∈ m) ψ n)

/-- The completed number operator has the same occupation-basis eigenvalue equation as the
algebraic number operator. -/
@[simp]
theorem completedNumberOperator_basisState (i : Mode) (n : Occupation Mode) :
    completedNumberOperator i (completedBasisState n) =
      if i ∈ n then completedBasisState n else 0 := by
  simpa [completedNumberOperator, completedBasisState] using
    (Common.completedCoordinateProjection_basisState
      (Config := Occupation Mode) (fun m : Occupation Mode => i ∈ m) n)

/-- The completed single-mode number operator agrees with the algebraic number operator on the
whole finite-support core, not only on individual basis states. -/
theorem completedNumberOperator_comp_algebraicToCompleted (i : Mode) :
    (completedNumberOperator i).toLinearMap.comp algebraicToCompleted =
      algebraicToCompleted.comp (numberOperator i) := by
  apply Finsupp.lhom_ext
  intro n c
  have hc : (Finsupp.single n c : OccupationFock Mode) = c • basisState n :=
    (Finsupp.smul_single_one n c).symm
  rw [hc]
  simp only [LinearMap.comp_apply, map_smul]
  by_cases hi : i ∈ n <;>
    simp [numberOperator_basisState, hi]

end
end Fermionic
end SecondQuantization
