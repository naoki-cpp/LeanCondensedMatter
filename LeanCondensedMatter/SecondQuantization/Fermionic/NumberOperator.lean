import LeanCondensedMatter.SecondQuantization.Fermionic.CanonicalAnticommutationRelations
import LeanCondensedMatter.SecondQuantization.Common.ExchangeCommutator

set_option linter.style.header false

/-!
# The fermionic number operator, and the reordering identity `c_i c_i† = id - N_i`

The fermionic counterpart of `Bosonic/NumberOperator.lean`: `numberOperator i := create i ∘
annihilate i`, its eigenvalue equation on basis states, and the reordering identity `c_i c_i† =
id - N_i` (from CAR's `{c_i, c_i†} = id`, via the unified `ζ`-commutator
`Common.exchangeCommutator`). Split out from `Hamiltonian.lean` (which still holds
`totalNumberOperator`/`freeHamiltonian`/`interactionHamiltonian`, all built on top of this) so
both statistics' number-operator layer live in symmetric files — mirroring
`Bosonic/NumberOperator.lean`'s `numberOperator`/`numberOperator_apply`/`numberOperator_basisState`/
`exchangeCommutator_annihilate_create_self`/`annihilate_comp_create_self` exactly, up to the sign
of `ζ`.
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode]

/-- **The single-mode number operator** `Nᵢ := aᵢ† aᵢ`. -/
noncomputable def numberOperator (i : Mode) :
    FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode :=
  (create i).comp (annihilate i)

theorem numberOperator_apply (i : Mode) (x : FockSpaceFermionic Mode) :
    numberOperator i x = create i (annihilate i x) :=
  rfl

/-- **The number-operator eigenvalue equation**, on basis states: `Nᵢ` acts as the identity on
occupied modes and as zero on unoccupied ones — occupation-number states are simultaneous
eigenvectors of every `numberOperator i`, with eigenvalue `0` or `1`. -/
theorem numberOperator_basisState (i : Mode) (n : FermionOccupation Mode) :
    numberOperator i (basisState n) = if i ∈ n then basisState n else 0 := by
  rw [numberOperator_apply]
  by_cases hi : i ∈ n
  · rw [if_pos hi]
    have hnotmem : i ∉ removeOccupation i n := Finset.notMem_erase i n
    have heq : insertOccupation i (removeOccupation i n) = n := by
      rw [insertOccupation, removeOccupation, Finset.insert_erase hi]
    rw [annihilate_basisState_of_mem hi, map_smul, create_basisState_of_not_mem hnotmem,
      fermionSign_removeOccupation_of_not_lt hi (lt_irrefl i), heq, smul_smul,
      fermionSign_sq_complex, one_smul]
  · rw [if_neg hi, annihilate_basisState_of_not_mem hi, map_zero]

/-- **`[c_i, c_i†]_ζ = id`, the fermionic case (`ζ = Statistics.zetaInt Statistics.fermion`)**:
CAR's anticommutator `{c_i, c_i†} = id` (`anticomm_annihilate_create`) is exactly
`Common.exchangeCommutator Statistics.fermion` — see `Common/ExchangeCommutator.lean`'s module
docstring, and `Bosonic/NumberOperator.lean`'s `exchangeCommutator_annihilate_create_self` for the
bosonic mirror. -/
theorem exchangeCommutator_annihilate_create_self (i : Mode) :
    Common.exchangeCommutator Statistics.fermion (annihilate i) (create i) =
      (LinearMap.id : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) := by
  rw [Common.exchangeCommutator, Statistics.zetaInt_fermion, Int.cast_neg, Int.cast_one,
    Common.zetaCommutator, neg_one_smul, sub_neg_eq_add]
  have h := anticomm_annihilate_create (Mode := Mode) i i
  rwa [if_pos rfl] at h

/-- **`c_i c_i† = id - N_i`**, from CAR's `{c_i, c_i†} = id`, via the unified `ζ`-commutator
reordering identity (`Common.comp_eq_id_add_of_zetaCommutator_eq_id`). -/
theorem annihilate_comp_create_self (i : Mode) :
    (annihilate i).comp (create i) = LinearMap.id - numberOperator i := by
  have h := Common.comp_eq_id_add_of_zetaCommutator_eq_id
    ((Statistics.zetaInt Statistics.fermion : ℤ) : ℂ)
    (exchangeCommutator_annihilate_create_self i)
  rw [Statistics.zetaInt_fermion, Int.cast_neg, Int.cast_one] at h
  rwa [neg_one_smul, ← sub_eq_add_neg] at h

end SecondQuantization
