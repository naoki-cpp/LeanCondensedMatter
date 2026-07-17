import LeanCondensedMatter.SecondQuantization.Bosonic.FockSpace
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Finsupp.LSum

set_option linter.style.header false

/-!
# Bosonic creation and annihilation operators

Phase B1 of Track D's bosonic line (`notes/roadmaps/second-quantization.md`): the creation and
annihilation operators `create i`, `annihilate i : FockSpaceBosonic Mode →ₗ[ℂ] FockSpaceBosonic
Mode`, defined on basis states and extended linearly.

Unlike the fermionic case, there is no Jordan–Wigner-style sign factor — bosonic modes commute,
not anticommute — but the basis-state action is **not** simply "add or remove an occupied mode"
either: the normalization carries a `√n` factor,
`a_i|n⟩ = √(n_i)|n - eᵢ⟩`, `a_i†|n⟩ = √(n_i + 1)|n + eᵢ⟩`,
matching the standard convention that makes the number operator `a_i† a_i` diagonal with integer
eigenvalue `n_i` (rather than, say, `n_i` itself with no square root, which would fail to satisfy
the canonical commutation relation `[a_i, a_i†] = 1`). This file proves the basis-level action
(vacuum, raising/lowering particle number) but stops short of CCR itself (`[a_i, a_j†] = δᵢⱼ`
etc.), which is a separate, not-yet-started future target — the `√n`/`√(n+1)` bookkeeping makes
that telescoping argument genuinely more involved than the fermionic CAR proof.
-/

namespace SecondQuantization
namespace Bosonic

variable {Mode : Type*} [DecidableEq Mode]

/-- **Creation, on a basis state.** `√(n_i + 1) • |n + eᵢ⟩`. -/
noncomputable def createBasis (i : Mode) (n : Occupation Mode) : FockSpaceBosonic Mode :=
  (Real.sqrt (n i + 1 : ℝ) : ℂ) • basisState (createOccupation i n)

/-- **Annihilation, on a basis state.** `0` if `i` is unoccupied; otherwise `√(n_i) • |n - eᵢ⟩`. -/
noncomputable def annihilateBasis (i : Mode) (n : Occupation Mode) : FockSpaceBosonic Mode :=
  if n i = 0 then 0 else (Real.sqrt (n i : ℝ) : ℂ) • basisState (removeOccupation i n)

/-- **The creation operator** at mode `i`, extended linearly from `createBasis`. -/
noncomputable def create (i : Mode) : FockSpaceBosonic Mode →ₗ[ℂ] FockSpaceBosonic Mode :=
  Finsupp.lift (FockSpaceBosonic Mode) ℂ (Occupation Mode) (createBasis i)

/-- **The annihilation operator** at mode `i`, extended linearly from `annihilateBasis`. -/
noncomputable def annihilate (i : Mode) : FockSpaceBosonic Mode →ₗ[ℂ] FockSpaceBosonic Mode :=
  Finsupp.lift (FockSpaceBosonic Mode) ℂ (Occupation Mode) (annihilateBasis i)

theorem create_basisState (i : Mode) (n : Occupation Mode) :
    create i (basisState n) = createBasis i n := by
  change Finsupp.lift _ ℂ _ (createBasis i) (Finsupp.single n 1) = createBasis i n
  simp [Finsupp.lift_apply, Finsupp.sum_single_index]

theorem annihilate_basisState (i : Mode) (n : Occupation Mode) :
    annihilate i (basisState n) = annihilateBasis i n := by
  change Finsupp.lift _ ℂ _ (annihilateBasis i) (Finsupp.single n 1) = annihilateBasis i n
  simp [Finsupp.lift_apply, Finsupp.sum_single_index]

/-- **Creation raises the occupation**: `a_i†|n⟩ = √(n_i + 1)|n + eᵢ⟩`, one more particle than `n`
(`particleNumber_createOccupation`). -/
theorem create_basisState_eq (i : Mode) (n : Occupation Mode) :
    create i (basisState n) = (Real.sqrt (n i + 1 : ℝ) : ℂ) • basisState (createOccupation i n) :=
  create_basisState i n

/-- **The vacuum has no particles to annihilate.** -/
@[simp]
theorem annihilate_basisState_of_zero {i : Mode} {n : Occupation Mode} (h : n i = 0) :
    annihilate i (basisState n) = 0 := by
  rw [annihilate_basisState, annihilateBasis, if_pos h]

/-- **Annihilation lowers the occupation**: `a_i|n⟩ = √(n_i)|n - eᵢ⟩`, one fewer particle than `n`
(`particleNumber_removeOccupation_of_pos`), when mode `i` is occupied. -/
theorem annihilate_basisState_of_pos {i : Mode} {n : Occupation Mode} (h : n i ≠ 0) :
    annihilate i (basisState n) =
      (Real.sqrt (n i : ℝ) : ℂ) • basisState (removeOccupation i n) := by
  rw [annihilate_basisState, annihilateBasis, if_neg h]

@[simp]
theorem annihilate_fockVacuum (i : Mode) :
    annihilate i (fockVacuum : FockSpaceBosonic Mode) = 0 :=
  annihilate_basisState_of_zero (by simp [vacuum])

end Bosonic
end SecondQuantization
