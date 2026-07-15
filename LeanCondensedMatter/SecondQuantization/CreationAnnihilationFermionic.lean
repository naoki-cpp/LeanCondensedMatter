import LeanCondensedMatter.SecondQuantization.FockSpaceFermionic
import Mathlib.LinearAlgebra.Finsupp.LSum

set_option linter.style.header false

/-!
# Fermionic creation and annihilation operators

Phase 4 of Track D's fermionic primary line (`notes/roadmaps/second-quantization.md`): the
creation and annihilation operators `create i`, `annihilate i : FockSpaceFermionic Mode →ₗ[ℂ]
FockSpaceFermionic Mode`, defined on basis states and extended linearly.

Unlike the bosonic case, these carry a **sign factor** (the Jordan–Wigner-style string): acting
with `create i`/`annihilate i` on the occupation state `n` picks up a factor `(-1)^k`, where `k`
is the number of *occupied* modes ordered strictly before `i`. This requires fixing a
`[LinearOrder Mode]` on the mode set (needed to make "before" meaningful) — the first place in
this track a mode ordering is required.

This file proves the basis-level action (vacuum, raising/lowering particle number, Pauli
exclusion) but stops short of CAR itself (`{aᵢ, aⱼ†} = δᵢⱼ` etc.), which is `CAR.lean`'s job.
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode]

/-- **The fermionic exchange sign** for acting at mode `i` on occupation state `n`: `(-1)^k`
where `k` is the number of modes in `n` ordered strictly before `i`. Used identically for both
`create i` and `annihilate i` (the sign is a property of *where* `i` sits relative to `n`, not of
which operation is being performed). -/
def fermionSign (i : Mode) (n : FermionOccupation Mode) : ℤ :=
  (-1) ^ (n.filter (· < i)).card

omit [DecidableEq Mode] in
@[simp]
theorem fermionSign_fermionVacuum (i : Mode) :
    fermionSign i (fermionVacuum : FermionOccupation Mode) = 1 := by
  simp [fermionSign, fermionVacuum]

/-- **Creation, on a basis state.** `0` if `i` is already occupied (Pauli exclusion); otherwise
the signed basis state with `i` newly occupied. -/
noncomputable def createBasis (i : Mode) (n : FermionOccupation Mode) : FockSpaceFermionic Mode :=
  if i ∈ n then 0 else (fermionSign i n : ℂ) • basisState (insertOccupation i n)

/-- **Annihilation, on a basis state.** `0` if `i` is unoccupied; otherwise the signed basis
state with `i` newly vacated. -/
noncomputable def annihilateBasis (i : Mode) (n : FermionOccupation Mode) :
    FockSpaceFermionic Mode :=
  if i ∈ n then (fermionSign i n : ℂ) • basisState (removeOccupation i n) else 0

/-- **The creation operator** at mode `i`, extended linearly from `createBasis`. -/
noncomputable def create (i : Mode) : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode :=
  Finsupp.lift (FockSpaceFermionic Mode) ℂ (FermionOccupation Mode) (createBasis i)

/-- **The annihilation operator** at mode `i`, extended linearly from `annihilateBasis`. -/
noncomputable def annihilate (i : Mode) : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode :=
  Finsupp.lift (FockSpaceFermionic Mode) ℂ (FermionOccupation Mode) (annihilateBasis i)

theorem create_basisState (i : Mode) (n : FermionOccupation Mode) :
    create i (basisState n) = createBasis i n := by
  change Finsupp.lift _ ℂ _ (createBasis i) (Finsupp.single n 1) = createBasis i n
  simp [Finsupp.lift_apply, Finsupp.sum_single_index]

theorem annihilate_basisState (i : Mode) (n : FermionOccupation Mode) :
    annihilate i (basisState n) = annihilateBasis i n := by
  change Finsupp.lift _ ℂ _ (annihilateBasis i) (Finsupp.single n 1) = annihilateBasis i n
  simp [Finsupp.lift_apply, Finsupp.sum_single_index]

/-- **Pauli exclusion.** Creating a particle in an already-occupied mode annihilates the state. -/
@[simp]
theorem create_basisState_of_mem {i : Mode} {n : FermionOccupation Mode} (h : i ∈ n) :
    create i (basisState n) = 0 := by
  rw [create_basisState, createBasis, if_pos h]

/-- **Creation raises the occupation.** Creating a particle in an unoccupied mode `i` produces
(up to the sign `fermionSign i n`) the basis state of `n` with `i` newly occupied — one more
particle than `n` (`fermionParticleNumber_insertOccupation_of_not_mem`). -/
theorem create_basisState_of_not_mem {i : Mode} {n : FermionOccupation Mode} (h : i ∉ n) :
    create i (basisState n) = (fermionSign i n : ℂ) • basisState (insertOccupation i n) := by
  rw [create_basisState, createBasis, if_neg h]

/-- **The empty mode cannot be annihilated.** -/
@[simp]
theorem annihilate_basisState_of_not_mem {i : Mode} {n : FermionOccupation Mode} (h : i ∉ n) :
    annihilate i (basisState n) = 0 := by
  rw [annihilate_basisState, annihilateBasis, if_neg h]

/-- **Annihilation lowers the occupation.** Annihilating a particle in an occupied mode `i`
produces (up to the sign `fermionSign i n`) the basis state of `n` with `i` newly vacated — one
fewer particle than `n` (`fermionParticleNumber_removeOccupation_of_mem`). -/
theorem annihilate_basisState_of_mem {i : Mode} {n : FermionOccupation Mode} (h : i ∈ n) :
    annihilate i (basisState n) = (fermionSign i n : ℂ) • basisState (removeOccupation i n) := by
  rw [annihilate_basisState, annihilateBasis, if_pos h]

/-- **The vacuum cannot be annihilated at any mode.** -/
@[simp]
theorem annihilate_fockVacuum (i : Mode) :
    annihilate i (fockVacuum : FockSpaceFermionic Mode) = 0 :=
  annihilate_basisState_of_not_mem (Finset.notMem_empty i)

/-- **Creating a particle in the vacuum** produces the single-particle basis state at mode `i`,
with sign `1` (no modes precede an empty occupation). -/
@[simp]
theorem create_fockVacuum (i : Mode) :
    create i (fockVacuum : FockSpaceFermionic Mode) =
      basisState ({i} : FermionOccupation Mode) := by
  have hnotmem : i ∉ (fermionVacuum : FermionOccupation Mode) := Finset.notMem_empty i
  rw [fockVacuum, create_basisState_of_not_mem hnotmem, fermionSign_fermionVacuum, Int.cast_one,
    one_smul, insertOccupation, fermionVacuum]
  congr 1

/-- **Creating twice in the same mode annihilates the state**, the basis-level shadow of Pauli
exclusion (`{aᵢ†, aᵢ†} = 0`, before CAR itself is stated in `CAR.lean`). -/
@[simp]
theorem create_create_basisState_self (i : Mode) (n : FermionOccupation Mode) :
    create i (create i (basisState n)) = 0 := by
  by_cases h : i ∈ n
  · rw [create_basisState_of_mem h, map_zero]
  · have hmem : i ∈ insertOccupation i n := Finset.mem_insert_self i n
    rw [create_basisState_of_not_mem h, map_smul, create_basisState_of_mem hmem, smul_zero]

end SecondQuantization
