import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.FockSpace
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Finsupp.LSum

set_option linter.style.header false

/-!
# Bosonic creation and annihilation operators

Creation and annihilation are defined on occupation-number basis states and extended linearly to
`FockSpace Mode`. Their basis-state normalization is

`a_i† |n⟩ = √(n_i + 1) |n + e_i⟩`,
`a_i |n⟩ = √n_i |n - e_i⟩`.

The square-root factors give the standard canonical commutation relations and make
`a_i† a_i` act with eigenvalue `n_i`.
-/

namespace SecondQuantization
namespace Bosonic

noncomputable section

variable {Mode : Type*}

/-- File-local classical decidable equality, kept out of public theorem signatures. -/
local instance instDecidableEqCreationAnnihilation : DecidableEq Mode := Classical.decEq Mode

/-- Creation on a basis state: `√(n_i + 1) • |n + e_i⟩`. -/
noncomputable def createBasis (i : Mode) (n : Occupation Mode) : FockSpace Mode :=
  (Real.sqrt (n i + 1 : ℝ) : ℂ) • basisState (createOccupation i n)

/-- Annihilation on a basis state, vanishing when mode `i` is unoccupied. -/
noncomputable def annihilateBasis (i : Mode) (n : Occupation Mode) : FockSpace Mode :=
  if n i = 0 then 0 else (Real.sqrt (n i : ℝ) : ℂ) • basisState (removeOccupation i n)

/-- The creation operator at mode `i`. -/
noncomputable def create (i : Mode) : FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  Finsupp.lift (FockSpace Mode) ℂ (Occupation Mode) (createBasis i)

/-- The annihilation operator at mode `i`. -/
noncomputable def annihilate (i : Mode) : FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  Finsupp.lift (FockSpace Mode) ℂ (Occupation Mode) (annihilateBasis i)

theorem create_basisState (i : Mode) (n : Occupation Mode) :
    create i (basisState n) = createBasis i n := by
  change Finsupp.lift _ ℂ _ (createBasis i) (Finsupp.single n 1) = createBasis i n
  simp [Finsupp.lift_apply, Finsupp.sum_single_index]

theorem annihilate_basisState (i : Mode) (n : Occupation Mode) :
    annihilate i (basisState n) = annihilateBasis i n := by
  change Finsupp.lift _ ℂ _ (annihilateBasis i) (Finsupp.single n 1) = annihilateBasis i n
  simp [Finsupp.lift_apply, Finsupp.sum_single_index]

/-- Creation raises the occupation at mode `i`. -/
theorem create_basisState_eq (i : Mode) (n : Occupation Mode) :
    create i (basisState n) = (Real.sqrt (n i + 1 : ℝ) : ℂ) • basisState (createOccupation i n) :=
  create_basisState i n

@[simp]
theorem annihilate_basisState_of_zero {i : Mode} {n : Occupation Mode} (h : n i = 0) :
    annihilate i (basisState n) = 0 := by
  rw [annihilate_basisState, annihilateBasis, if_pos h]

/-- Annihilation lowers a nonzero occupation at mode `i`. -/
theorem annihilate_basisState_of_pos {i : Mode} {n : Occupation Mode} (h : n i ≠ 0) :
    annihilate i (basisState n) =
      (Real.sqrt (n i : ℝ) : ℂ) • basisState (removeOccupation i n) := by
  rw [annihilate_basisState, annihilateBasis, if_neg h]

/-- Uniform basis-state action of annihilation. The zero-occupation case is absorbed by `√0 = 0`,
so downstream proofs do not need to branch on whether mode `i` is occupied. -/
theorem annihilate_basisState_eq (i : Mode) (n : Occupation Mode) :
    annihilate i (basisState n) =
      (Real.sqrt (n i : ℝ) : ℂ) • basisState (removeOccupation i n) := by
  by_cases h : n i = 0
  · rw [annihilate_basisState_of_zero h, h]
    simp
  · exact annihilate_basisState_of_pos h

@[simp]
theorem annihilate_fockVacuum (i : Mode) :
    annihilate i (fockVacuum : FockSpace Mode) = 0 :=
  annihilate_basisState_of_zero (by simp [vacuum])

end

end Bosonic
end SecondQuantization
