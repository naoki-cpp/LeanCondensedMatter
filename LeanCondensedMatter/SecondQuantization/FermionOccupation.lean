import Mathlib.Data.Finset.Card

set_option linter.style.header false

/-!
# Fermionic occupation-number states

Track D's primary line now targets the finite-mode *fermionic* case first (Linked Cluster
Theorem groundwork, `notes/roadmaps/second-quantization.md`). Pauli exclusion means a fermionic
occupation-number state is fully determined by *which* modes are occupied — no mode can hold more
than one particle — so `FermionOccupation Mode := Finset Mode` (the set of occupied modes), unlike
the bosonic case's `Mode →₀ ℕ` (`BosonOccupation.lean`).

This file only covers the occupation-number bookkeeping (vacuum, particle number, inserting/
removing a mode from the occupied set). It deliberately stops short of the fermionic creation/
annihilation operators, CAR, and the sign (Jordan–Wigner-style) factors that come with them —
those belong to a later file (`CreationAnnihilationFermionic.lean`) once this bookkeeping layer is
in place.
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode]

/-- **Fermionic occupation-number state.** The set of occupied modes; Pauli exclusion means each
mode is either occupied (present) or empty (absent), with no multiplicity. -/
abbrev FermionOccupation (Mode : Type*) := Finset Mode

/-- **The vacuum state**: no mode occupied. -/
def fermionVacuum : FermionOccupation Mode := ∅

/-- **The total particle number** of a fermionic occupation-number state: the number of occupied
modes. -/
def fermionParticleNumber (n : FermionOccupation Mode) : ℕ := n.card

omit [DecidableEq Mode] in
@[simp]
theorem fermionParticleNumber_fermionVacuum :
    fermionParticleNumber (fermionVacuum : FermionOccupation Mode) = 0 :=
  Finset.card_empty

/-- **Occupying mode `i`.** Adds `i` to the occupied set; a no-op if `i` was already occupied
(Pauli exclusion — this is the set-level bookkeeping only, without the sign factor that
accompanies the actual fermionic creation operator). -/
def insertOccupation (i : Mode) (n : FermionOccupation Mode) : FermionOccupation Mode :=
  insert i n

/-- **Vacating mode `i`.** Removes `i` from the occupied set; a no-op if `i` was already empty. -/
def removeOccupation (i : Mode) (n : FermionOccupation Mode) : FermionOccupation Mode :=
  n.erase i

theorem fermionParticleNumber_insertOccupation_of_not_mem {i : Mode} {n : FermionOccupation Mode}
    (h : i ∉ n) :
    fermionParticleNumber (insertOccupation i n) = fermionParticleNumber n + 1 :=
  Finset.card_insert_of_notMem h

theorem fermionParticleNumber_insertOccupation_of_mem {i : Mode} {n : FermionOccupation Mode}
    (h : i ∈ n) :
    fermionParticleNumber (insertOccupation i n) = fermionParticleNumber n := by
  rw [fermionParticleNumber, fermionParticleNumber, insertOccupation, Finset.insert_eq_self.2 h]

theorem fermionParticleNumber_removeOccupation_of_mem {i : Mode} {n : FermionOccupation Mode}
    (h : i ∈ n) :
    fermionParticleNumber (removeOccupation i n) + 1 = fermionParticleNumber n :=
  Finset.card_erase_add_one h

theorem fermionParticleNumber_removeOccupation_of_not_mem {i : Mode} {n : FermionOccupation Mode}
    (h : i ∉ n) :
    fermionParticleNumber (removeOccupation i n) = fermionParticleNumber n := by
  rw [fermionParticleNumber, fermionParticleNumber, removeOccupation, Finset.erase_eq_of_notMem h]

end SecondQuantization
