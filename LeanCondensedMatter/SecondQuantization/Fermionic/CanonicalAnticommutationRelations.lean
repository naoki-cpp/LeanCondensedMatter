import LeanCondensedMatter.SecondQuantization.Fermionic.CreationAnnihilation

set_option linter.style.header false

/-!
# The canonical anticommutation relations

Phase 5 of Track D's fermionic primary line (`notes/roadmaps/second-quantization.md`): the
canonical anticommutation relations (CAR) for the fermionic creation/annihilation operators of
`CreationAnnihilationFermionic.lean`:

* `{aᵢ, aⱼ} = 0` (`anticomm_annihilate_annihilate`)
* `{aᵢ†, aⱼ†} = 0` (`anticomm_create_create`)
* `{aᵢ, aⱼ†} = δᵢⱼ` (`anticomm_annihilate_create`)

The file is named out in full (not abbreviated `CAR.lean`) so the module name itself says what it
proves.
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode]

/-! ## The anticommutator, and reduction to basis states -/

omit [LinearOrder Mode] in
/-- **The anticommutator** of two linear endomorphisms, `{A, B} := AB + BA`. -/
noncomputable def anticomm (A B : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode :=
  A.comp B + B.comp A

omit [LinearOrder Mode] in
theorem anticomm_apply (A B : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode)
    (x : FockSpaceFermionic Mode) : anticomm A B x = A (B x) + B (A x) :=
  rfl

omit [LinearOrder Mode] in
/-- Two `ℤ`-signed multiples of the same basis vector cancel when the underlying integers do:
the arithmetic core shared by all three CAR proofs below (creation-creation, annihilation-
annihilation, and the off-diagonal case of annihilation-creation). -/
theorem cancel_cast_smul_smul {a b c d : ℤ} (h : a * b + c * d = 0)
    (v : FockSpaceFermionic Mode) :
    (a : ℂ) • (b : ℂ) • v + (c : ℂ) • (d : ℂ) • v = 0 := by
  rw [smul_smul, smul_smul, ← Int.cast_mul, ← Int.cast_mul, ← add_smul, ← Int.cast_add, h,
    Int.cast_zero, zero_smul]

/-! ## Sign lemmas: how `fermionSign` changes under inserting/removing an unrelated mode -/

theorem fermionSign_insertOccupation_of_lt {i k : Mode} {n : FermionOccupation Mode}
    (hk : k ∉ n) (h : k < i) :
    fermionSign i (insertOccupation k n) = -fermionSign i n := by
  have hfilter : (insertOccupation k n).filter (· < i) = insert k (n.filter (· < i)) := by
    rw [insertOccupation, Finset.filter_insert, if_pos h]
  have hknotmem : k ∉ n.filter (· < i) := fun hmem => hk (Finset.mem_of_mem_filter k hmem)
  rw [fermionSign, fermionSign, hfilter, Finset.card_insert_of_notMem hknotmem, pow_succ']
  ring

theorem fermionSign_insertOccupation_of_not_lt {i k : Mode} {n : FermionOccupation Mode}
    (_hk : k ∉ n) (h : ¬k < i) :
    fermionSign i (insertOccupation k n) = fermionSign i n := by
  have hfilter : (insertOccupation k n).filter (· < i) = n.filter (· < i) := by
    rw [insertOccupation, Finset.filter_insert, if_neg h]
  rw [fermionSign, fermionSign, hfilter]

theorem fermionSign_removeOccupation_of_lt {i k : Mode} {n : FermionOccupation Mode}
    (hk : k ∈ n) (h : k < i) :
    fermionSign i (removeOccupation k n) = -fermionSign i n := by
  have hfilter : (removeOccupation k n).filter (· < i) = (n.filter (· < i)).erase k := by
    rw [removeOccupation, Finset.filter_erase]
  have hkmem : k ∈ n.filter (· < i) := Finset.mem_filter.2 ⟨hk, h⟩
  have hcard : ((n.filter (· < i)).erase k).card + 1 = (n.filter (· < i)).card :=
    Finset.card_erase_add_one hkmem
  rw [fermionSign, fermionSign, hfilter, ← hcard, pow_succ]
  ring

theorem fermionSign_removeOccupation_of_not_lt {i k : Mode} {n : FermionOccupation Mode}
    (_hk : k ∈ n) (h : ¬k < i) :
    fermionSign i (removeOccupation k n) = fermionSign i n := by
  have hfilter : (removeOccupation k n).filter (· < i) = n.filter (· < i) := by
    rw [removeOccupation, Finset.filter_erase, Finset.erase_eq_of_notMem]
    exact fun hmem => h (Finset.mem_filter.1 hmem).2
  rw [fermionSign, fermionSign, hfilter]

omit [DecidableEq Mode] in
theorem fermionSign_sq (i : Mode) (n : FermionOccupation Mode) :
    fermionSign i n * fermionSign i n = 1 := by
  rw [fermionSign, ← pow_add, ← two_mul, pow_mul]
  norm_num

omit [DecidableEq Mode] in
@[simp]
theorem fermionSign_sq_complex (i : Mode) (n : FermionOccupation Mode) :
    (fermionSign i n : ℂ) * (fermionSign i n : ℂ) = 1 := by
  rw [← Int.cast_mul, fermionSign_sq, Int.cast_one]

/-- **The sign-cancellation identity behind `{aᵢ†, aⱼ†} = 0`.** For distinct, both-unoccupied
modes `i, j`, the two orders of inserting `i` then `j` (vs. `j` then `i`) pick up opposite signs.
Case-split on which of `i`, `j` comes first in the mode order. -/
theorem fermionSign_create_create_cancel {i j : Mode} {n : FermionOccupation Mode} (hij : i ≠ j)
    (hi : i ∉ n) (hj : j ∉ n) :
    fermionSign j n * fermionSign i (insertOccupation j n) +
      fermionSign i n * fermionSign j (insertOccupation i n) = 0 := by
  rcases lt_or_lt_iff_ne.mpr hij with h | h
  · rw [fermionSign_insertOccupation_of_not_lt hj (not_lt.mpr h.le),
      fermionSign_insertOccupation_of_lt hi h]
    ring
  · rw [fermionSign_insertOccupation_of_lt hj h,
      fermionSign_insertOccupation_of_not_lt hi (not_lt.mpr h.le)]
    ring

/-- **The sign-cancellation identity behind `{aᵢ, aⱼ} = 0`.** For distinct, both-occupied modes
`i, j`, the two orders of removing `i` then `j` (vs. `j` then `i`) pick up opposite signs. -/
theorem fermionSign_annihilate_annihilate_cancel {i j : Mode} {n : FermionOccupation Mode}
    (hij : i ≠ j) (hi : i ∈ n) (hj : j ∈ n) :
    fermionSign j n * fermionSign i (removeOccupation j n) +
      fermionSign i n * fermionSign j (removeOccupation i n) = 0 := by
  rcases lt_or_lt_iff_ne.mpr hij with h | h
  · rw [fermionSign_removeOccupation_of_not_lt hj (not_lt.mpr h.le),
      fermionSign_removeOccupation_of_lt hi h]
    ring
  · rw [fermionSign_removeOccupation_of_lt hj h,
      fermionSign_removeOccupation_of_not_lt hi (not_lt.mpr h.le)]
    ring

/-! ## `{aᵢ†, aⱼ†} = 0` -/

theorem anticomm_create_create_basisState (i j : Mode) (n : FermionOccupation Mode) :
    anticomm (create i) (create j) (basisState n) = 0 := by
  rw [anticomm_apply]
  rcases eq_or_ne i j with rfl | hij
  · simp
  by_cases hj : j ∈ n
  · rw [create_basisState_of_mem hj, map_zero, zero_add]
    by_cases hi : i ∈ n
    · simp [create_basisState_of_mem hi]
    · have hjmem : j ∈ insertOccupation i n := Finset.mem_insert_of_mem hj
      rw [create_basisState_of_not_mem hi, map_smul, create_basisState_of_mem hjmem, smul_zero]
  by_cases hi : i ∈ n
  · have hij' : i ∈ insertOccupation j n := Finset.mem_insert_of_mem hi
    rw [create_basisState_of_not_mem hj, map_smul, create_basisState_of_mem hij',
      create_basisState_of_mem hi, map_zero, smul_zero, zero_add]
  · have hinj : i ∉ insertOccupation j n := by simp [insertOccupation, hij, hi]
    have hjni : j ∉ insertOccupation i n := by simp [insertOccupation, Ne.symm hij, hj]
    have hswap :
        insertOccupation i (insertOccupation j n) = insertOccupation j (insertOccupation i n) := by
      rw [insertOccupation, insertOccupation, insertOccupation, insertOccupation,
        Finset.insert_comm]
    rw [create_basisState_of_not_mem hj, map_smul, create_basisState_of_not_mem hinj,
      create_basisState_of_not_mem hi, map_smul, create_basisState_of_not_mem hjni, hswap]
    exact cancel_cast_smul_smul (fermionSign_create_create_cancel hij hi hj) _

theorem anticomm_create_create (i j : Mode) : anticomm (create i) (create j) = 0 :=
  linearMap_ext_basisState fun n => anticomm_create_create_basisState i j n

/-- **`cᵢ† cᵢ† = 0`**: the same-mode special case of `anticomm_create_create`, `{cᵢ†, cᵢ†} =
2 cᵢ† cᵢ† = 0`, hence `cᵢ† cᵢ† = 0` (`ℂ` has no `2`-torsion). -/
theorem create_comp_self (i : Mode) : (create i).comp (create i) = 0 := by
  have h := anticomm_create_create (Mode := Mode) i i
  rw [anticomm] at h
  have h2 : (2 : ℂ) • ((create i).comp (create i)) = 0 := by rw [two_smul]; exact h
  rcases smul_eq_zero.mp h2 with h0 | h0
  · exact absurd h0 (by norm_num)
  · exact h0

/-! ## `{aᵢ, aⱼ} = 0` -/

theorem anticomm_annihilate_annihilate_basisState (i j : Mode) (n : FermionOccupation Mode) :
    anticomm (annihilate i) (annihilate j) (basisState n) = 0 := by
  rw [anticomm_apply]
  rcases eq_or_ne i j with rfl | hij
  · by_cases hi : i ∈ n
    · have hnotmem : i ∉ removeOccupation i n := Finset.notMem_erase i n
      simp [annihilate_basisState_of_mem hi, annihilate_basisState_of_not_mem hnotmem]
    · simp [annihilate_basisState_of_not_mem hi]
  by_cases hj : j ∈ n
  · by_cases hi : i ∈ n
    · have hij' : i ∈ removeOccupation j n := Finset.mem_erase.2 ⟨hij, hi⟩
      have hji' : j ∈ removeOccupation i n := Finset.mem_erase.2 ⟨Ne.symm hij, hj⟩
      rw [annihilate_basisState_of_mem hj, map_smul, annihilate_basisState_of_mem hij',
        annihilate_basisState_of_mem hi, map_smul, annihilate_basisState_of_mem hji']
      have hswap : removeOccupation i (removeOccupation j n) =
          removeOccupation j (removeOccupation i n) := by
        rw [removeOccupation, removeOccupation, removeOccupation, removeOccupation,
          Finset.erase_right_comm]
      rw [hswap]
      exact cancel_cast_smul_smul (fermionSign_annihilate_annihilate_cancel hij hi hj) _
    · have hinj : i ∉ removeOccupation j n := fun h => hi (Finset.mem_of_mem_erase h)
      rw [annihilate_basisState_of_mem hj, map_smul, annihilate_basisState_of_not_mem hinj,
        smul_zero, annihilate_basisState_of_not_mem hi, map_zero, zero_add]
  · by_cases hi : i ∈ n
    · have hjni : j ∉ removeOccupation i n := fun h => hj (Finset.mem_of_mem_erase h)
      rw [annihilate_basisState_of_not_mem hj, map_zero, annihilate_basisState_of_mem hi,
        map_smul, annihilate_basisState_of_not_mem hjni, smul_zero, zero_add]
    · rw [annihilate_basisState_of_not_mem hj, map_zero, annihilate_basisState_of_not_mem hi,
        map_zero, zero_add]

theorem anticomm_annihilate_annihilate (i j : Mode) : anticomm (annihilate i) (annihilate j) = 0 :=
  linearMap_ext_basisState fun n => anticomm_annihilate_annihilate_basisState i j n

/-- **`cᵢ cᵢ = 0`**: the same-mode special case of `anticomm_annihilate_annihilate`, the
creation-side mirror of `create_comp_self`. -/
theorem annihilate_comp_self (i : Mode) : (annihilate i).comp (annihilate i) = 0 := by
  have h := anticomm_annihilate_annihilate (Mode := Mode) i i
  rw [anticomm] at h
  have h2 : (2 : ℂ) • ((annihilate i).comp (annihilate i)) = 0 := by rw [two_smul]; exact h
  rcases smul_eq_zero.mp h2 with h0 | h0
  · exact absurd h0 (by norm_num)
  · exact h0

/-! ## `{aᵢ, aⱼ†} = δᵢⱼ` -/

theorem anticomm_annihilate_create_basisState (i j : Mode) (n : FermionOccupation Mode) :
    anticomm (annihilate i) (create j) (basisState n) = if i = j then basisState n else 0 := by
  rw [anticomm_apply]
  rcases eq_or_ne i j with rfl | hij
  · rw [if_pos rfl]
    by_cases hi : i ∈ n
    · have hnotmem : i ∉ removeOccupation i n := Finset.notMem_erase i n
      have heq : insertOccupation i (removeOccupation i n) = n := by
        rw [insertOccupation, removeOccupation, Finset.insert_erase hi]
      rw [create_basisState_of_mem hi, map_zero, zero_add, annihilate_basisState_of_mem hi,
        map_smul, create_basisState_of_not_mem hnotmem,
        fermionSign_removeOccupation_of_not_lt hi (lt_irrefl i), heq, smul_smul,
        fermionSign_sq_complex, one_smul]
    · have hmem : i ∈ insertOccupation i n := Finset.mem_insert_self i n
      have heq : removeOccupation i (insertOccupation i n) = n := by
        rw [removeOccupation, insertOccupation, Finset.erase_insert hi]
      rw [annihilate_basisState_of_not_mem hi, map_zero, add_zero,
        create_basisState_of_not_mem hi, map_smul, annihilate_basisState_of_mem hmem,
        fermionSign_insertOccupation_of_not_lt hi (lt_irrefl i), heq, smul_smul,
        fermionSign_sq_complex, one_smul]
  · rw [if_neg hij]
    by_cases hj : j ∈ n
    · rw [create_basisState_of_mem hj, map_zero, zero_add]
      by_cases hi : i ∈ n
      · have hij' : j ∈ removeOccupation i n := Finset.mem_erase.2 ⟨Ne.symm hij, hj⟩
        rw [annihilate_basisState_of_mem hi, map_smul, create_basisState_of_mem hij', smul_zero]
      · rw [annihilate_basisState_of_not_mem hi, map_zero]
    · by_cases hi : i ∈ n
      · have hij' : i ∈ insertOccupation j n := Finset.mem_insert_of_mem hi
        have hjni : j ∉ removeOccupation i n := fun h => hj (Finset.mem_of_mem_erase h)
        have hswap : removeOccupation i (insertOccupation j n) =
            insertOccupation j (removeOccupation i n) :=
          Finset.erase_insert_of_ne (Ne.symm hij)
        rw [create_basisState_of_not_mem hj, map_smul, annihilate_basisState_of_mem hij',
          annihilate_basisState_of_mem hi, map_smul, create_basisState_of_not_mem hjni, hswap]
        rcases lt_or_lt_iff_ne.mpr hij with h | h
        · rw [fermionSign_insertOccupation_of_not_lt hj (not_lt.mpr h.le),
            fermionSign_removeOccupation_of_lt hi h]
          exact cancel_cast_smul_smul (by ring) _
        · rw [fermionSign_insertOccupation_of_lt hj h,
            fermionSign_removeOccupation_of_not_lt hi (not_lt.mpr h.le)]
          exact cancel_cast_smul_smul (by ring) _
      · have hinj : i ∉ insertOccupation j n := by simp [insertOccupation, hij, hi]
        rw [create_basisState_of_not_mem hj, map_smul, annihilate_basisState_of_not_mem hinj,
          smul_zero, annihilate_basisState_of_not_mem hi, map_zero, zero_add]

theorem anticomm_annihilate_create (i j : Mode) :
    anticomm (annihilate i) (create j) = if i = j then LinearMap.id else 0 := by
  rcases eq_or_ne i j with rfl | hij
  · rw [if_pos rfl]
    exact linearMap_ext_basisState fun n => by
      rw [anticomm_annihilate_create_basisState, if_pos rfl, LinearMap.id_apply]
  · rw [if_neg hij]
    exact linearMap_ext_basisState fun n => by
      rw [anticomm_annihilate_create_basisState, if_neg hij, LinearMap.zero_apply]

omit [LinearOrder Mode] in
/-- **The anticommutator is symmetric**, `{A, B} = {B, A}` — immediate from `anticomm`'s own
definition `A ∘ B + B ∘ A` via `add_comm`. -/
theorem anticomm_comm (A B : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    anticomm A B = anticomm B A := by
  rw [anticomm, anticomm, add_comm]

/-- **`{cᵢ†, cⱼ} = δᵢⱼ`**: the creation-first mirror of `anticomm_annihilate_create`, via
`anticomm_comm`. -/
theorem anticomm_create_annihilate (i j : Mode) :
    anticomm (create i) (annihilate j) = if i = j then LinearMap.id else 0 := by
  rw [anticomm_comm, anticomm_annihilate_create]
  simp only [eq_comm]

end SecondQuantization
