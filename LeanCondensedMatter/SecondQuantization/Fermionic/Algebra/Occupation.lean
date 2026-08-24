import Mathlib.Data.Finset.Card
import LeanCondensedMatter.SecondQuantization.Common.Algebra.OccupationBasis

set_option linter.style.header false

/-!
# Fermionic occupation-number states

Pauli exclusion means a fermionic occupation-number state is fully determined by *which* modes are
occupied — no mode can hold more than one particle — so `Occupation Mode := Finset Mode` (the set
of occupied modes), unlike the bosonic case's `Mode →₀ ℕ` in `Bosonic/Algebra/Occupation.lean`.

This file owns the occupation-number bookkeeping: vacuum, particle number, and inserting or
removing a mode from the occupied set. Creation and annihilation operators are defined separately in
`CreationAnnihilation.lean`, and their canonical anticommutation relations are proved in
`CanonicalAnticommutationRelations.lean`.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [DecidableEq Mode]

/-- **Fermionic occupation-number state.** The set of occupied modes; Pauli exclusion means each
mode is either occupied (present) or empty (absent), with no multiplicity. -/
abbrev Occupation (Mode : Type*) := Finset Mode

/-- **The vacuum occupation configuration**: no mode occupied. -/
def vacuum : Occupation Mode := ∅

/-- **The total particle number** of a fermionic occupation-number state: the number of occupied
modes. -/
def particleNumber (n : Occupation Mode) : ℕ := n.card


omit [DecidableEq Mode] in
@[simp]
theorem particleNumber_vacuum :
    particleNumber (vacuum : Occupation Mode) = 0 :=
  Finset.card_empty

/-- **Occupying mode `i`.** Adds `i` to the occupied set; a no-op if `i` was already occupied
(Pauli exclusion — this is the set-level bookkeeping only, without the sign factor that
accompanies the actual fermionic creation operator). -/
def insertOccupation (i : Mode) (n : Occupation Mode) : Occupation Mode :=
  insert i n

/-- **Vacating mode `i`.** Removes `i` from the occupied set; a no-op if `i` was already empty. -/
def removeOccupation (i : Mode) (n : Occupation Mode) : Occupation Mode :=
  n.erase i

theorem particleNumber_insertOccupation_of_not_mem {i : Mode} {n : Occupation Mode}
    (h : i ∉ n) :
    particleNumber (insertOccupation i n) = particleNumber n + 1 :=
  Finset.card_insert_of_notMem h

theorem particleNumber_insertOccupation_of_mem {i : Mode} {n : Occupation Mode}
    (h : i ∈ n) :
    particleNumber (insertOccupation i n) = particleNumber n := by
  rw [particleNumber, particleNumber, insertOccupation, Finset.insert_eq_self.2 h]

theorem particleNumber_removeOccupation_of_mem {i : Mode} {n : Occupation Mode}
    (h : i ∈ n) :
    particleNumber (removeOccupation i n) + 1 = particleNumber n :=
  Finset.card_erase_add_one h

theorem particleNumber_removeOccupation_of_not_mem {i : Mode} {n : Occupation Mode}
    (h : i ∉ n) :
    particleNumber (removeOccupation i n) = particleNumber n := by
  rw [particleNumber, particleNumber, removeOccupation, Finset.erase_eq_of_notMem h]

/-! ## The `Common.OccupationBasis` instance -/

/-- **The fermionic occupation-basis instance**: `Occupation Mode` reads off each mode's
occupation number as `1`/`0` (occupied/empty) — the concrete side of `Common.OccupationBasis`'s
shared interface, mirroring `SecondQuantization.Bosonic.occupationBasis`
(`Bosonic/Algebra/Occupation.lean`). -/
instance occupationBasis : Common.OccupationBasis Mode (Occupation Mode) where
  vacuum := vacuum
  occupation n i := if i ∈ n then 1 else 0
  occupation_vacuum i := by simp [vacuum]
  finiteSupport n := (Finset.finite_toSet n).subset fun i hi => by
    by_contra hin
    exact hi (if_neg hin)
  ext {m n} h := Finset.ext fun i => by
    have hi := h i
    by_cases hm : i ∈ m <;> by_cases hn : i ∈ n <;> simp_all

end Fermionic
end SecondQuantization
