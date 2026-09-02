import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.CanonicalAnticommutationRelations
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.ExchangeAlgebra
import LeanCondensedMatter.SecondQuantization.Common.Algebra.ExchangeCommutator
import Mathlib.Tactic.Abel

set_option linter.style.header false

/-!
# The fermionic number operator, and the reordering identity `c_i c_i† = id - N_i`

The fermionic counterpart of `Bosonic/Algebra/NumberOperator.lean`: `numberOperator i := create i ∘
annihilate i`, its eigenvalue equation on basis states, and the reordering identity `c_i c_i† =
id - N_i` (from CAR's `{c_i, c_i†} = id`, via the unified `ζ`-commutator
`Common.exchangeCommutator`). Split out from `Hamiltonian.lean` (which still holds
`totalNumberOperator`/`freeHamiltonian`/`interactionHamiltonian`, all built on top of this) so
both statistics' number-operator layer live in symmetric files — mirroring
`Bosonic/Algebra/NumberOperator.lean`'s `numberOperator`/`numberOperator_apply`/`numberOperator_basisState`/
`exchangeCommutator_annihilate_create_self`/`annihilate_comp_create_self` exactly, up to the sign
of `ζ`.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode]

/-- **The single-mode number operator** `Nᵢ := aᵢ† aᵢ`. -/
noncomputable def numberOperator (i : Mode) :
    OccupationFock Mode →ₗ[ℂ] OccupationFock Mode :=
  (create i).comp (annihilate i)

theorem numberOperator_apply (i : Mode) (x : OccupationFock Mode) :
    numberOperator i x = create i (annihilate i x) :=
  rfl

/-- **The number-operator eigenvalue equation**, on basis states: `Nᵢ` acts as the identity on
occupied modes and as zero on unoccupied ones — occupation-number states are simultaneous
eigenvectors of every `numberOperator i`, with eigenvalue `0` or `1`. -/
theorem numberOperator_basisState (i : Mode) (n : Occupation Mode) :
    numberOperator i (basisState n) = if i ∈ n then basisState n else 0 := by
  rw [numberOperator_apply]
  by_cases hi : i ∈ n
  · rw [if_pos hi]
    have hnotmem : i ∉ removeOccupation i n := Finset.notMem_erase i n
    have heq : insertOccupation i (removeOccupation i n) = n := by
      rw [insertOccupation, removeOccupation, Finset.insert_erase hi]
    rw [annihilate_basisState_of_mem hi, map_smul, create_basisState_of_not_mem hnotmem,
      fermionSign_removeOccupation_of_not_lt (lt_irrefl i), heq, smul_smul,
      fermionSign_sq_complex, one_smul]
  · rw [if_neg hi, annihilate_basisState_of_not_mem hi, map_zero]

/-- **`[c_i, c_i†]_ζ = id`, the fermionic case (`ζ = Common.Statistics.zetaInt Common.Statistics.fermion`)**: an
instance of `Common.exchangeCommutator_annihilate_create_self`, via the fermionic
`Common.ExchangeAlgebra` instance (`Fermionic/Algebra/ExchangeAlgebra.lean`), whose `annihilate`/`create`
fields are literally `Fermionic.annihilate`/`create`. -/
theorem exchangeCommutator_annihilate_create_self (i : Mode) :
    Common.exchangeCommutator Common.Statistics.fermion (annihilate i) (create i) =
      (LinearMap.id : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :=
  Common.exchangeCommutator_annihilate_create_self (Config := Occupation Mode) i

/-- **`c_i c_i† = id - N_i`**, an instance of `Common.annihilate_comp_create_self`. -/
theorem annihilate_comp_create_self (i : Mode) :
    (annihilate i).comp (create i) = LinearMap.id - numberOperator i := by
  have h := Common.annihilate_comp_create_self (s := Common.Statistics.fermion)
    (Config := Occupation Mode) i
  rwa [Common.Statistics.zetaInt_fermion, Int.cast_neg, Int.cast_one, neg_one_smul,
    ← sub_eq_add_neg] at h

/-- **`Nᵢ` is idempotent**: `Nᵢ ∘ Nᵢ = Nᵢ`, directly from the number-operator eigenvalue equation
(occupation-number basis states are simultaneous eigenvectors with eigenvalue `0` or `1`). -/
theorem numberOperator_comp_self (i : Mode) :
    (numberOperator i).comp (numberOperator i) = numberOperator i := by
  apply Common.linearMap_ext_basisState
  intro n
  change ((numberOperator i).comp (numberOperator i)) (basisState n) =
    numberOperator i (basisState n)
  rw [LinearMap.comp_apply, numberOperator_basisState]
  split_ifs with h
  · rw [numberOperator_basisState, if_pos h]
  · rw [map_zero]

/-- **`cᵢ cᵢ†` is idempotent**: `(cᵢ cᵢ†)(cᵢ cᵢ†) = cᵢ cᵢ†`, from `cᵢ cᵢ† = id - Nᵢ`
(`annihilate_comp_create_self`) and `Nᵢ`'s idempotency. -/
theorem annihilate_comp_create_comp_self (i : Mode) :
    ((annihilate i).comp (create i)).comp ((annihilate i).comp (create i)) =
      (annihilate i).comp (create i) := by
  simp only [annihilate_comp_create_self, LinearMap.sub_comp, LinearMap.comp_sub,
    LinearMap.id_comp, LinearMap.comp_id, numberOperator_comp_self]
  abel

/-- **`cᵢ cᵢ† + cᵢ† cᵢ = id`**, CAR's anticommutation relation rearranged: `cᵢ cᵢ† = id - Nᵢ`
together with `Nᵢ = cᵢ† cᵢ` by definition. -/
theorem annihilate_comp_create_add_create_comp_annihilate (i : Mode) :
    (annihilate i).comp (create i) + (create i).comp (annihilate i) =
      (LinearMap.id : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) := by
  rw [annihilate_comp_create_self, show (create i).comp (annihilate i) = numberOperator i from rfl]
  abel

end Fermionic
end SecondQuantization
