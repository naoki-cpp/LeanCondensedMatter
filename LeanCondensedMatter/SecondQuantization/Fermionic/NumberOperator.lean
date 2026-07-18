import LeanCondensedMatter.SecondQuantization.Fermionic.CanonicalAnticommutationRelations

set_option linter.style.header false

/-!
# The fermionic number operator

The fermionic counterpart of `Bosonic/NumberOperator.lean`: `numberOperator i := create i ∘
annihilate i` and its eigenvalue equation on basis states. Split out from `Hamiltonian.lean` (which
still holds `totalNumberOperator`/`freeHamiltonian`/`interactionHamiltonian`, all built on top of
this) so both statistics' number-operator layer live in symmetric files — mirroring
`Bosonic/NumberOperator.lean`'s split from the (not-yet-written) bosonic Hamiltonian file.
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

end SecondQuantization
