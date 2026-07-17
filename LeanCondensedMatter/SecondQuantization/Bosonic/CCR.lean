import LeanCondensedMatter.SecondQuantization.Bosonic.CreationAnnihilation

set_option linter.style.header false

/-!
# The canonical commutation relations

Phase B1d of Track D's bosonic line (`notes/roadmaps/second-quantization.md`): the canonical
commutation relations (CCR) for the bosonic creation/annihilation operators of
`CreationAnnihilation.lean`:

* `[aᵢ, aⱼ] = 0` (`comm_annihilate_annihilate`)
* `[aᵢ†, aⱼ†] = 0` (`comm_create_create`)
* `[aᵢ, aⱼ†] = δᵢⱼ` (`comm_annihilate_create`)

Unlike the fermionic CAR proof (`Fermionic/CanonicalAnticommutationRelations.lean`), there is no
sign bookkeeping to track — bosonic modes commute — but the `√n`/`√(n+1)` normalization
factors need their own telescoping identity, `Real.mul_self_sqrt`, to collapse `√n · √n = n`
at the diagonal (`i = j`) case.
-/

namespace SecondQuantization
namespace Bosonic

variable {Mode : Type*} [DecidableEq Mode]

/-! ## The commutator, and reduction to basis states -/

/-- **The commutator** of two linear endomorphisms, `[A, B] := AB - BA`. -/
noncomputable def comm (A B : FockSpaceBosonic Mode →ₗ[ℂ] FockSpaceBosonic Mode) :
    FockSpaceBosonic Mode →ₗ[ℂ] FockSpaceBosonic Mode :=
  A.comp B - B.comp A

theorem comm_apply (A B : FockSpaceBosonic Mode →ₗ[ℂ] FockSpaceBosonic Mode)
    (x : FockSpaceBosonic Mode) : comm A B x = A (B x) - B (A x) :=
  rfl

/-- **The square-root normalization factor squares back to the (cast) natural number it was taken
from** — the arithmetic core of every diagonal (`i = j`) case below. -/
theorem sqrt_natCast_mul_self (k : ℕ) :
    (Real.sqrt (k : ℝ) : ℂ) * (Real.sqrt (k : ℝ) : ℂ) = (k : ℂ) := by
  have h : Real.sqrt (k : ℝ) * Real.sqrt (k : ℝ) = (k : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg k)
  exact_mod_cast h

/-! ## `[aᵢ†, aⱼ†] = 0` -/

theorem comm_create_create_basisState (i j : Mode) (n : Occupation Mode) :
    comm (create i) (create j) (basisState n) = 0 := by
  rw [comm_apply]
  rcases eq_or_ne i j with rfl | hij
  · exact sub_self _
  rw [create_basisState_eq, map_smul, create_basisState_eq, create_basisState_eq, map_smul,
    create_basisState_eq, createOccupation_apply_ne hij, createOccupation_apply_ne hij.symm,
    smul_smul, smul_smul, createOccupation_comm i j n, mul_comm, sub_self]

theorem comm_create_create (i j : Mode) : comm (create i) (create j) = 0 :=
  linearMap_ext_basisState fun n => by rw [comm_create_create_basisState, LinearMap.zero_apply]

/-! ## `[aᵢ, aⱼ] = 0` -/

theorem comm_annihilate_annihilate_basisState (i j : Mode) (n : Occupation Mode) :
    comm (annihilate i) (annihilate j) (basisState n) = 0 := by
  rw [comm_apply]
  rcases eq_or_ne i j with rfl | hij
  · exact sub_self _
  by_cases hj : n j = 0
  · by_cases hi : n i = 0
    · rw [annihilate_basisState_of_zero hj, map_zero, annihilate_basisState_of_zero hi, map_zero,
        sub_self]
    · have hj' : removeOccupation i n j = 0 := by
        rw [removeOccupation_apply_ne hij.symm]; exact hj
      rw [annihilate_basisState_of_zero hj, map_zero, annihilate_basisState_of_pos hi, map_smul,
        annihilate_basisState_of_zero hj', smul_zero, sub_zero]
  · by_cases hi : n i = 0
    · have hi' : removeOccupation j n i = 0 := by
        rw [removeOccupation_apply_ne hij]; exact hi
      rw [annihilate_basisState_of_zero hi, map_zero, annihilate_basisState_of_pos hj, map_smul,
        annihilate_basisState_of_zero hi', smul_zero, zero_sub, neg_eq_zero]
    · have hj' : removeOccupation i n j ≠ 0 := by
        rw [removeOccupation_apply_ne hij.symm]; exact hj
      have hi' : removeOccupation j n i ≠ 0 := by
        rw [removeOccupation_apply_ne hij]; exact hi
      rw [annihilate_basisState_of_pos hj, map_smul, annihilate_basisState_of_pos hi',
        annihilate_basisState_of_pos hi, map_smul, annihilate_basisState_of_pos hj',
        removeOccupation_apply_ne hij, removeOccupation_apply_ne hij.symm,
        smul_smul, smul_smul, removeOccupation_comm hij, mul_comm, sub_self]

theorem comm_annihilate_annihilate (i j : Mode) : comm (annihilate i) (annihilate j) = 0 :=
  linearMap_ext_basisState fun n => by
    rw [comm_annihilate_annihilate_basisState, LinearMap.zero_apply]

/-! ## `[aᵢ, aⱼ†] = δᵢⱼ` -/

/-- **`a_i a_i†` acts diagonally with eigenvalue `n_i + 1`**: `a_i(a_i†|n⟩) = (n_i + 1)|n⟩`. Half
of the diagonal (`i = j`) CCR telescoping argument. -/
theorem annihilate_create_basisState_same (i : Mode) (n : Occupation Mode) :
    annihilate i (create i (basisState n)) = ((n i : ℂ) + 1) • basisState n := by
  have h1 : createOccupation i n i ≠ 0 := by rw [createOccupation_apply_same]; omega
  have hscalar :
      (Real.sqrt ((n i : ℝ) + 1) : ℂ) * (Real.sqrt (createOccupation i n i : ℝ) : ℂ)
        = (n i : ℂ) + 1 := by
    rw [createOccupation_apply_same]
    push_cast
    exact_mod_cast Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ (n i : ℝ) + 1)
  rw [create_basisState_eq, map_smul, annihilate_basisState_of_pos h1,
    removeOccupation_createOccupation, smul_smul, hscalar]

/-- **`a_i† a_i` acts diagonally with eigenvalue `n_i`**: `a_i†(a_i|n⟩) = n_i|n⟩`. The other half
of the diagonal (`i = j`) CCR telescoping argument. -/
theorem create_annihilate_basisState_same (i : Mode) (n : Occupation Mode) :
    create i (annihilate i (basisState n)) = (n i : ℂ) • basisState n := by
  by_cases h : n i = 0
  · rw [annihilate_basisState_of_zero h, map_zero, h]
    simp
  · have heq : (removeOccupation i n i : ℝ) + 1 = (n i : ℝ) := by
      rw [removeOccupation_apply_same, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr h)]
      push_cast; ring
    have hscalar :
        (Real.sqrt ((removeOccupation i n i : ℝ) + 1) : ℂ) = (Real.sqrt (n i : ℝ) : ℂ) := by
      rw [heq]
    rw [annihilate_basisState_of_pos h, map_smul, create_basisState_eq, hscalar,
      createOccupation_removeOccupation_of_pos h, smul_smul, sqrt_natCast_mul_self]

theorem comm_annihilate_create_basisState (i j : Mode) (n : Occupation Mode) :
    comm (annihilate i) (create j) (basisState n) = if i = j then basisState n else 0 := by
  rw [comm_apply]
  rcases eq_or_ne i j with rfl | hij
  · rw [if_pos rfl, annihilate_create_basisState_same, create_annihilate_basisState_same,
      ← sub_smul]
    have harith : ((n i : ℂ) + 1) - (n i : ℂ) = 1 := by ring
    rw [harith, one_smul]
  · rw [if_neg hij]
    by_cases hi : n i = 0
    · rw [create_basisState_eq, map_smul,
        annihilate_basisState_of_zero (show createOccupation j n i = 0 by
          rw [createOccupation_apply_ne hij]; exact hi),
        smul_zero, annihilate_basisState_of_zero hi, map_zero, sub_zero]
    · have hcj : createOccupation j n i ≠ 0 := by
        rw [createOccupation_apply_ne hij]; exact hi
      have hswap :
          removeOccupation i (createOccupation j n) = createOccupation j (removeOccupation i n) :=
        removeOccupation_createOccupation_of_ne hij n
      have hrj : (removeOccupation i n) j = n j := removeOccupation_apply_ne hij.symm n
      rw [create_basisState_eq, map_smul, annihilate_basisState_of_pos hcj,
        createOccupation_apply_ne hij, hswap, annihilate_basisState_of_pos hi, map_smul,
        create_basisState_eq, hrj, smul_smul, smul_smul, mul_comm, sub_self]

theorem comm_annihilate_create (i j : Mode) :
    comm (annihilate i) (create j) =
      if i = j then
        (LinearMap.id : FockSpaceBosonic Mode →ₗ[ℂ] FockSpaceBosonic Mode)
      else 0 := by
  rcases eq_or_ne i j with rfl | hij
  · rw [if_pos rfl]
    exact linearMap_ext_basisState fun n => by
      rw [comm_annihilate_create_basisState, if_pos rfl, LinearMap.id_apply]
  · rw [if_neg hij]
    exact linearMap_ext_basisState fun n => by
      rw [comm_annihilate_create_basisState, if_neg hij, LinearMap.zero_apply]

end Bosonic
end SecondQuantization
