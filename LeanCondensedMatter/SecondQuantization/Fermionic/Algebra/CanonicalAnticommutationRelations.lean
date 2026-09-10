import LeanCondensedMatter.Analysis.Operator.ZetaCommutator
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.CreationAnnihilation

set_option linter.style.header false

/-!
# The canonical anticommutation relations

This module proves the canonical anticommutation relations (CAR) for the fermionic creation and
annihilation operators defined in `CreationAnnihilation.lean`:

* `{aᵢ, aⱼ} = 0` (`anticomm_annihilate_annihilate`)
* `{aᵢ†, aⱼ†} = 0` (`anticomm_create_create`)
* `{aᵢ, aⱼ†} = δᵢⱼ` (`anticomm_annihilate_create`)

The endpoint theorems state these relations directly through the canonical `ζ = -1`
`LinearMap.zetaCommutator`; this module does not define a second raw anticommutator operator.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode]

omit [LinearOrder Mode] in
/-- Two `ℤ`-signed multiples of the same basis vector cancel when the underlying integers do:
the arithmetic core shared by all three CAR proofs below (creation-creation, annihilation-
annihilation, and the off-diagonal case of annihilation-creation). -/
theorem cancel_cast_smul_smul {a b c d : ℤ} (h : a * b + c * d = 0)
    (v : OccupationFock Mode) :
    (a : ℂ) • (b : ℂ) • v + (c : ℂ) • (d : ℂ) • v = 0 := by
  rw [smul_smul, smul_smul, ← Int.cast_mul, ← Int.cast_mul, ← add_smul, ← Int.cast_add, h,
    Int.cast_zero, zero_smul]

/-! ## Sign lemmas: how `fermionSign` changes under inserting/removing an unrelated mode -/

theorem fermionSign_insertOccupation_of_lt {i k : Mode} {n : Occupation Mode}
    (hk : k ∉ n) (h : k < i) :
    fermionSign i (insertOccupation k n) = -fermionSign i n := by
  have hfilter : (insertOccupation k n).filter (· < i) = insert k (n.filter (· < i)) := by
    rw [insertOccupation, Finset.filter_insert, if_pos h]
  have hknotmem : k ∉ n.filter (· < i) := fun hmem => hk (Finset.mem_of_mem_filter k hmem)
  rw [fermionSign, fermionSign, hfilter, Finset.card_insert_of_notMem hknotmem, pow_succ']
  ring

theorem fermionSign_insertOccupation_of_not_lt {i k : Mode} {n : Occupation Mode}
    (h : ¬k < i) :
    fermionSign i (insertOccupation k n) = fermionSign i n := by
  have hfilter : (insertOccupation k n).filter (· < i) = n.filter (· < i) := by
    rw [insertOccupation, Finset.filter_insert, if_neg h]
  rw [fermionSign, fermionSign, hfilter]

theorem fermionSign_removeOccupation_of_lt {i k : Mode} {n : Occupation Mode}
    (hk : k ∈ n) (h : k < i) :
    fermionSign i (removeOccupation k n) = -fermionSign i n := by
  have hfilter : (removeOccupation k n).filter (· < i) = (n.filter (· < i)).erase k := by
    rw [removeOccupation, Finset.filter_erase]
  have hkmem : k ∈ n.filter (· < i) := Finset.mem_filter.2 ⟨hk, h⟩
  have hcard : ((n.filter (· < i)).erase k).card + 1 = (n.filter (· < i)).card :=
    Finset.card_erase_add_one hkmem
  rw [fermionSign, fermionSign, hfilter, ← hcard, pow_succ]
  ring

theorem fermionSign_removeOccupation_of_not_lt {i k : Mode} {n : Occupation Mode}
    (h : ¬k < i) :
    fermionSign i (removeOccupation k n) = fermionSign i n := by
  have hfilter : (removeOccupation k n).filter (· < i) = n.filter (· < i) := by
    rw [removeOccupation, Finset.filter_erase, Finset.erase_eq_of_notMem]
    exact fun hmem => h (Finset.mem_filter.1 hmem).2
  rw [fermionSign, fermionSign, hfilter]

theorem fermionSign_sq (i : Mode) (n : Occupation Mode) :
    fermionSign i n * fermionSign i n = 1 := by
  rw [fermionSign, ← pow_add, ← two_mul, pow_mul]
  norm_num

@[simp]
theorem fermionSign_sq_complex (i : Mode) (n : Occupation Mode) :
    (fermionSign i n : ℂ) * (fermionSign i n : ℂ) = 1 := by
  rw [← Int.cast_mul, fermionSign_sq, Int.cast_one]

/-- **The sign-cancellation identity behind `{aᵢ†, aⱼ†} = 0`.** For distinct, both-unoccupied
modes `i, j`, the two orders of inserting `i` then `j` (vs. `j` then `i`) pick up opposite signs.
Case-split on which of `i`, `j` comes first in the mode order. -/
theorem fermionSign_create_create_cancel {i j : Mode} {n : Occupation Mode} (hij : i ≠ j)
    (hi : i ∉ n) (hj : j ∉ n) :
    fermionSign j n * fermionSign i (insertOccupation j n) +
      fermionSign i n * fermionSign j (insertOccupation i n) = 0 := by
  rcases lt_or_lt_iff_ne.mpr hij with h | h
  · rw [fermionSign_insertOccupation_of_not_lt (not_lt.mpr h.le),
      fermionSign_insertOccupation_of_lt hi h]
    ring
  · rw [fermionSign_insertOccupation_of_lt hj h,
      fermionSign_insertOccupation_of_not_lt (not_lt.mpr h.le)]
    ring

/-- **The sign-cancellation identity behind `{aᵢ, aⱼ} = 0`.** For distinct, both-occupied modes
`i, j`, the two orders of removing `i` then `j` (vs. `j` then `i`) pick up opposite signs. -/
theorem fermionSign_annihilate_annihilate_cancel {i j : Mode} {n : Occupation Mode}
    (hij : i ≠ j) (hi : i ∈ n) (hj : j ∈ n) :
    fermionSign j n * fermionSign i (removeOccupation j n) +
      fermionSign i n * fermionSign j (removeOccupation i n) = 0 := by
  rcases lt_or_lt_iff_ne.mpr hij with h | h
  · rw [fermionSign_removeOccupation_of_not_lt (not_lt.mpr h.le),
      fermionSign_removeOccupation_of_lt hi h]
    ring
  · rw [fermionSign_removeOccupation_of_lt hj h,
      fermionSign_removeOccupation_of_not_lt (not_lt.mpr h.le)]
    ring

/-! ## Uniform signed-toggle form of the ladder operators -/

private def createCoeff (i : Mode) (n : Occupation Mode) : ℤ :=
  if i ∈ n then 0 else fermionSign i n

private def annihilateCoeff (i : Mode) (n : Occupation Mode) : ℤ :=
  if i ∈ n then fermionSign i n else 0

private theorem create_basisState_toggle (i : Mode) (n : Occupation Mode) :
    create i (basisState n) =
      (createCoeff i n : ℂ) • basisState (toggleOccupation i n) := by
  by_cases h : i ∈ n
  · rw [create_basisState_of_mem h]
    simp [createCoeff, h]
  · rw [create_basisState_of_not_mem h, toggleOccupation_of_not_mem h]
    simp [createCoeff, h]

private theorem annihilate_basisState_toggle (i : Mode) (n : Occupation Mode) :
    annihilate i (basisState n) =
      (annihilateCoeff i n : ℂ) • basisState (toggleOccupation i n) := by
  by_cases h : i ∈ n
  · rw [annihilate_basisState_of_mem h, toggleOccupation_of_mem h]
    simp [annihilateCoeff, h]
  · rw [annihilate_basisState_of_not_mem h]
    simp [annihilateCoeff, h]

private theorem createCoeff_cancel (i j : Mode) (n : Occupation Mode) :
    createCoeff j n * createCoeff i (toggleOccupation j n) +
      createCoeff i n * createCoeff j (toggleOccupation i n) = 0 := by
  rcases eq_or_ne i j with rfl | hij
  · by_cases hi : i ∈ n
    · simp [createCoeff, hi]
    · simp [createCoeff, hi, insertOccupation]
  · by_cases hi : i ∈ n
    · by_cases hj : j ∈ n
      · simp [createCoeff, hi, hj]
      · simp [createCoeff, hi, hj, insertOccupation, hij]
    · by_cases hj : j ∈ n
      · simp [createCoeff, hi, hj, insertOccupation, Ne.symm hij]
      · simpa [createCoeff, hi, hj, insertOccupation, hij, Ne.symm hij] using
          fermionSign_create_create_cancel hij hi hj

private theorem annihilateCoeff_cancel (i j : Mode) (n : Occupation Mode) :
    annihilateCoeff j n * annihilateCoeff i (toggleOccupation j n) +
      annihilateCoeff i n * annihilateCoeff j (toggleOccupation i n) = 0 := by
  rcases eq_or_ne i j with rfl | hij
  · by_cases hi : i ∈ n
    · simp [annihilateCoeff, hi, removeOccupation]
    · simp [annihilateCoeff, hi]
  · by_cases hi : i ∈ n
    · by_cases hj : j ∈ n
      · simpa [annihilateCoeff, hi, hj, removeOccupation, hij, Ne.symm hij] using
          fermionSign_annihilate_annihilate_cancel hij hi hj
      · simp [annihilateCoeff, hi, hj, removeOccupation]
    · by_cases hj : j ∈ n <;>
        simp [annihilateCoeff, hi, hj, removeOccupation]

private theorem fermionSign_annihilate_create_cancel {i j : Mode} {n : Occupation Mode}
    (hij : i ≠ j) (hi : i ∈ n) (hj : j ∉ n) :
    fermionSign j n * fermionSign i (insertOccupation j n) +
      fermionSign i n * fermionSign j (removeOccupation i n) = 0 := by
  rcases lt_or_lt_iff_ne.mpr hij with h | h
  · rw [fermionSign_insertOccupation_of_not_lt (not_lt.mpr h.le),
      fermionSign_removeOccupation_of_lt hi h]
    ring
  · rw [fermionSign_insertOccupation_of_lt hj h,
      fermionSign_removeOccupation_of_not_lt (not_lt.mpr h.le)]
    ring

private theorem annihilateCreateCoeff_cancel_of_ne {i j : Mode} (hij : i ≠ j)
    (n : Occupation Mode) :
    createCoeff j n * annihilateCoeff i (toggleOccupation j n) +
      annihilateCoeff i n * createCoeff j (toggleOccupation i n) = 0 := by
  by_cases hi : i ∈ n
  · by_cases hj : j ∈ n
    · simp [createCoeff, annihilateCoeff, hi, hj, removeOccupation, hij, Ne.symm hij]
    · simpa [createCoeff, annihilateCoeff, hi, hj, insertOccupation, removeOccupation,
        hij, Ne.symm hij] using fermionSign_annihilate_create_cancel hij hi hj
  · by_cases hj : j ∈ n <;>
      simp [createCoeff, annihilateCoeff, hi, hj, insertOccupation, removeOccupation,
        hij, Ne.symm hij]

private theorem annihilateCreateCoeff_same (i : Mode) (n : Occupation Mode) :
    createCoeff i n * annihilateCoeff i (toggleOccupation i n) +
      annihilateCoeff i n * createCoeff i (toggleOccupation i n) = 1 := by
  by_cases hi : i ∈ n
  · have hnot : i ∉ removeOccupation i n := by simp [removeOccupation]
    rw [toggleOccupation_of_mem hi]
    simp [createCoeff, annihilateCoeff, hi, hnot,
      fermionSign_removeOccupation_of_not_lt (lt_irrefl i), fermionSign_sq]
  · have hmem : i ∈ insertOccupation i n := by simp [insertOccupation]
    rw [toggleOccupation_of_not_mem hi]
    simp [createCoeff, annihilateCoeff, hi, hmem,
      fermionSign_insertOccupation_of_not_lt (lt_irrefl i), fermionSign_sq]

/-! ## `{aᵢ†, aⱼ†} = 0` -/

theorem anticomm_create_create_basisState (i j : Mode) (n : Occupation Mode) :
    LinearMap.zetaCommutator (-1) (create i) (create j) (basisState n) = 0 := by
  rw [LinearMap.zetaCommutator_apply, neg_one_smul, sub_neg_eq_add,
    create_basisState_toggle, map_smul, create_basisState_toggle,
    create_basisState_toggle, map_smul, create_basisState_toggle,
    toggleOccupation_comm i j n]
  exact cancel_cast_smul_smul (createCoeff_cancel i j n) _

theorem anticomm_create_create (i j : Mode) :
    LinearMap.zetaCommutator (-1) (create i) (create j) = 0 := by
  apply Common.linearMap_ext_basisState
  intro n
  change LinearMap.zetaCommutator (-1) (create i) (create j) (basisState n) =
    (0 : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (basisState n)
  rw [anticomm_create_create_basisState, LinearMap.zero_apply]

/-- **`cᵢ† cᵢ† = 0`**: the same-mode consequence of `{cᵢ†, cᵢ†} = 0`. -/
theorem create_comp_self (i : Mode) : (create i).comp (create i) = 0 := by
  have h := anticomm_create_create (Mode := Mode) i i
  rw [LinearMap.zetaCommutator_self] at h
  norm_num at h
  exact h

/-! ## `{aᵢ, aⱼ} = 0` -/

theorem anticomm_annihilate_annihilate_basisState (i j : Mode) (n : Occupation Mode) :
    LinearMap.zetaCommutator (-1) (annihilate i) (annihilate j) (basisState n) = 0 := by
  rw [LinearMap.zetaCommutator_apply, neg_one_smul, sub_neg_eq_add,
    annihilate_basisState_toggle, map_smul, annihilate_basisState_toggle,
    annihilate_basisState_toggle, map_smul, annihilate_basisState_toggle,
    toggleOccupation_comm i j n]
  exact cancel_cast_smul_smul (annihilateCoeff_cancel i j n) _

theorem anticomm_annihilate_annihilate (i j : Mode) :
    LinearMap.zetaCommutator (-1) (annihilate i) (annihilate j) = 0 := by
  apply Common.linearMap_ext_basisState
  intro n
  change LinearMap.zetaCommutator (-1) (annihilate i) (annihilate j) (basisState n) =
    (0 : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (basisState n)
  rw [anticomm_annihilate_annihilate_basisState, LinearMap.zero_apply]

/-- **`cᵢ cᵢ = 0`**: the same-mode consequence of `{cᵢ, cᵢ} = 0`. -/
theorem annihilate_comp_self (i : Mode) : (annihilate i).comp (annihilate i) = 0 := by
  have h := anticomm_annihilate_annihilate (Mode := Mode) i i
  rw [LinearMap.zetaCommutator_self] at h
  norm_num at h
  exact h

/-! ## `{aᵢ, aⱼ†} = δᵢⱼ` -/

theorem anticomm_annihilate_create_basisState (i j : Mode) (n : Occupation Mode) :
    LinearMap.zetaCommutator (-1) (annihilate i) (create j) (basisState n) =
      if i = j then basisState n else 0 := by
  rw [LinearMap.zetaCommutator_apply, neg_one_smul, sub_neg_eq_add,
    create_basisState_toggle, map_smul, annihilate_basisState_toggle,
    annihilate_basisState_toggle, map_smul, create_basisState_toggle]
  rcases eq_or_ne i j with rfl | hij
  · rw [if_pos rfl, toggleOccupation_involutive i n]
    rw [smul_smul, smul_smul, ← Int.cast_mul, ← Int.cast_mul, ← add_smul, ← Int.cast_add,
      annihilateCreateCoeff_same, Int.cast_one, one_smul]
  · rw [if_neg hij, toggleOccupation_comm i j n]
    exact cancel_cast_smul_smul (annihilateCreateCoeff_cancel_of_ne hij n) _

theorem anticomm_annihilate_create (i j : Mode) :
    LinearMap.zetaCommutator (-1) (annihilate i) (create j) =
      if i = j then LinearMap.id else 0 := by
  rcases eq_or_ne i j with rfl | hij
  · rw [if_pos rfl]
    exact Common.linearMap_ext_basisState fun n => by
      change LinearMap.zetaCommutator (-1) (annihilate i) (create i) (basisState n) =
        (LinearMap.id : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (basisState n)
      rw [anticomm_annihilate_create_basisState, if_pos rfl, LinearMap.id_apply]
  · rw [if_neg hij]
    exact Common.linearMap_ext_basisState fun n => by
      change LinearMap.zetaCommutator (-1) (annihilate i) (create j) (basisState n) =
        (0 : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (basisState n)
      rw [anticomm_annihilate_create_basisState, if_neg hij, LinearMap.zero_apply]

/-- **`{cᵢ†, cⱼ} = δᵢⱼ`**: the creation-first mirror of `anticomm_annihilate_create`, obtained
from the generic `ζ = -1` swap rule. -/
theorem anticomm_create_annihilate (i j : Mode) :
    LinearMap.zetaCommutator (-1) (create i) (annihilate j) =
      if i = j then LinearMap.id else 0 := by
  calc
    LinearMap.zetaCommutator (-1) (create i) (annihilate j) =
        LinearMap.zetaCommutator (-1) (annihilate j) (create i) := by
      simpa using
        (LinearMap.zetaCommutator_swap_of_sq_eq_one
          (-1 : ℂ) (by norm_num) (annihilate j) (create i))
    _ = if j = i then LinearMap.id else 0 := anticomm_annihilate_create j i
    _ = if i = j then LinearMap.id else 0 := by simp only [eq_comm]

end Fermionic
end SecondQuantization
