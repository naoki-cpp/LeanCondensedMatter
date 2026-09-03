import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.CreationAnnihilation

set_option linter.style.header false

/-!
# Canonical commutation relations

The bosonic creation and annihilation operators satisfy

* `[a_i, a_j] = 0`,
* `[a_i†, a_j†] = 0`,
* `[a_i, a_j†] = δ_ij`.

The basis-state proofs account explicitly for the square-root normalization of the ladder
operators. `Bosonic.ExchangeAlgebra` packages these relations through the statistics-independent
`Common.exchangeCommutator` interface.
-/

namespace SecondQuantization
namespace Bosonic

noncomputable section

variable {Mode : Type*}

/-- File-local classical decidable equality, kept out of public theorem signatures. -/
local instance instDecidableEqCCR : DecidableEq Mode := Classical.decEq Mode

/-- The ordinary commutator of bosonic Fock-space endomorphisms. -/
noncomputable def comm (A B : FockSpace Mode →ₗ[ℂ] FockSpace Mode) :
    FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  A.comp B - B.comp A

theorem comm_apply (A B : FockSpace Mode →ₗ[ℂ] FockSpace Mode)
    (x : FockSpace Mode) : comm A B x = A (B x) - B (A x) :=
  rfl

/-- The square-root normalization factor squares to its natural-number argument. -/
theorem sqrt_natCast_mul_self (k : ℕ) :
    (Real.sqrt (k : ℝ) : ℂ) * (Real.sqrt (k : ℝ) : ℂ) = (k : ℂ) := by
  have h : Real.sqrt (k : ℝ) * Real.sqrt (k : ℝ) = (k : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg k)
  exact_mod_cast h

/-! ## `[a_i†, a_j†] = 0` -/

theorem comm_create_create_basisState (i j : Mode) (n : Occupation Mode) :
    comm (create i) (create j) (basisState n) = 0 := by
  rw [comm_apply]
  rcases eq_or_ne i j with rfl | hij
  · exact sub_self _
  rw [create_basisState_eq, map_smul, create_basisState_eq, create_basisState_eq, map_smul,
    create_basisState_eq, createOccupation_apply_ne hij, createOccupation_apply_ne hij.symm,
    smul_smul, smul_smul, createOccupation_comm i j n, mul_comm, sub_self]

theorem comm_create_create (i j : Mode) : comm (create i) (create j) = 0 :=
  Common.linearMap_ext_basisState fun n => by
    change comm (create i) (create j) (basisState n) = 0
    rw [comm_create_create_basisState]

/-! ## `[a_i, a_j] = 0` -/

theorem comm_annihilate_annihilate_basisState (i j : Mode) (n : Occupation Mode) :
    comm (annihilate i) (annihilate j) (basisState n) = 0 := by
  rw [comm_apply]
  rcases eq_or_ne i j with rfl | hij
  · exact sub_self _
  rw [annihilate_basisState_eq, map_smul, annihilate_basisState_eq,
    annihilate_basisState_eq, map_smul, annihilate_basisState_eq,
    removeOccupation_apply_ne hij, removeOccupation_apply_ne hij.symm,
    smul_smul, smul_smul, removeOccupation_comm hij, mul_comm, sub_self]

theorem comm_annihilate_annihilate (i j : Mode) : comm (annihilate i) (annihilate j) = 0 :=
  Common.linearMap_ext_basisState fun n => by
    change comm (annihilate i) (annihilate j) (basisState n) = 0
    rw [comm_annihilate_annihilate_basisState]

/-! ## `[a_i, a_j†] = δ_ij` -/

/-- `a_i a_i†` acts diagonally with eigenvalue `n_i + 1`. -/
theorem annihilate_create_basisState_same (i : Mode) (n : Occupation Mode) :
    annihilate i (create i (basisState n)) = ((n i : ℂ) + 1) • basisState n := by
  have hscalar :
      (Real.sqrt ((n i : ℝ) + 1) : ℂ) * (Real.sqrt (createOccupation i n i : ℝ) : ℂ)
        = (n i : ℂ) + 1 := by
    rw [createOccupation_apply_same]
    push_cast
    exact_mod_cast Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ (n i : ℝ) + 1)
  rw [create_basisState_eq, map_smul, annihilate_basisState_eq,
    removeOccupation_createOccupation, smul_smul, hscalar]

/-- `a_i† a_i` acts diagonally with eigenvalue `n_i`. -/
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
  · rw [if_neg hij, create_basisState_eq, map_smul, annihilate_basisState_eq,
      createOccupation_apply_ne hij, annihilate_basisState_eq, map_smul, create_basisState_eq,
      removeOccupation_apply_ne hij.symm, removeOccupation_createOccupation_of_ne hij n,
      smul_smul, smul_smul, mul_comm, sub_self]

theorem comm_annihilate_create (i j : Mode) :
    comm (annihilate i) (create j) =
      if i = j then
        (LinearMap.id : FockSpace Mode →ₗ[ℂ] FockSpace Mode)
      else 0 := by
  rcases eq_or_ne i j with rfl | hij
  · rw [if_pos rfl]
    exact Common.linearMap_ext_basisState fun n => by
      change comm (annihilate i) (create i) (basisState n) = basisState n
      rw [comm_annihilate_create_basisState, if_pos rfl]
  · rw [if_neg hij]
    exact Common.linearMap_ext_basisState fun n => by
      change comm (annihilate i) (create j) (basisState n) = 0
      rw [comm_annihilate_create_basisState, if_neg hij]

/-- The reverse mixed CCR, `[aᵢ†, aⱼ] = -δᵢⱼ`. -/
theorem comm_create_annihilate (i j : Mode) :
    comm (create i) (annihilate j) =
      if i = j then -(LinearMap.id : FockSpace Mode →ₗ[ℂ] FockSpace Mode) else 0 := by
  rw [show comm (create i) (annihilate j) = -comm (annihilate j) (create i) by
    simp only [comm]
    abel]
  rw [comm_annihilate_create]
  by_cases h : i = j
  · subst j
    simp
  · simp [h, Ne.symm h]

end

end Bosonic
end SecondQuantization
