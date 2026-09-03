import Mathlib.Data.Finset.Card
import LeanCondensedMatter.SecondQuantization.Common.Algebra.OccupationBasis

set_option linter.style.header false

/-!
# Fermionic occupation-number states

Pauli exclusion means a fermionic occupation-number state is fully determined by *which* modes are
occupied — no mode can hold more than one particle — so `Occupation Mode := Finset Mode` (the set
of occupied modes), unlike the bosonic case's `Mode →₀ ℕ` in `Bosonic/Algebra/Occupation.lean`.

This file owns the occupation-number bookkeeping: vacuum, particle number, and inserting, removing,
or toggling a mode in the occupied set. Creation and annihilation operators are defined separately
in `CreationAnnihilation.lean`, and their canonical anticommutation relations are proved in
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

/-- Toggle one fermionic mode. This is the common occupation reindexing underlying creation and
annihilation, independent of any Hilbert-space completion. -/
def toggleOccupation (i : Mode) (n : Occupation Mode) : Occupation Mode :=
  if i ∈ n then removeOccupation i n else insertOccupation i n

@[simp]
theorem mem_toggleOccupation (i : Mode) (n : Occupation Mode) :
    i ∈ toggleOccupation i n ↔ i ∉ n := by
  by_cases h : i ∈ n
  · simp [toggleOccupation, h, removeOccupation]
  · simp [toggleOccupation, h, insertOccupation]

theorem mem_toggleOccupation_of_ne {i j : Mode} (h : j ≠ i) (n : Occupation Mode) :
    j ∈ toggleOccupation i n ↔ j ∈ n := by
  by_cases hi : i ∈ n
  · simp [toggleOccupation, hi, removeOccupation, h]
  · simp [toggleOccupation, hi, insertOccupation, h]

@[simp]
theorem toggleOccupation_of_mem {i : Mode} {n : Occupation Mode} (h : i ∈ n) :
    toggleOccupation i n = removeOccupation i n := by
  simp [toggleOccupation, h]

@[simp]
theorem toggleOccupation_of_not_mem {i : Mode} {n : Occupation Mode} (h : i ∉ n) :
    toggleOccupation i n = insertOccupation i n := by
  simp [toggleOccupation, h]

@[simp]
theorem toggleOccupation_involutive (i : Mode) :
    Function.Involutive (toggleOccupation i) := by
  intro n
  by_cases h : i ∈ n
  · simp [toggleOccupation, h, removeOccupation, insertOccupation]
  · simp [toggleOccupation, h, removeOccupation, insertOccupation]

/-- Toggling two modes commutes. -/
theorem toggleOccupation_comm (i j : Mode) (n : Occupation Mode) :
    toggleOccupation i (toggleOccupation j n) =
      toggleOccupation j (toggleOccupation i n) := by
  rcases eq_or_ne i j with rfl | hij
  · rfl
  ext k
  by_cases hki : k = i
  · subst k
    simp only [mem_toggleOccupation, mem_toggleOccupation_of_ne hij]
  · by_cases hkj : k = j
    · subst k
      simp only [mem_toggleOccupation, mem_toggleOccupation_of_ne (Ne.symm hij)]
    · simp only [mem_toggleOccupation_of_ne hki, mem_toggleOccupation_of_ne hkj]

/-- Toggling one mode is an equivalence of the full occupation basis. -/
def toggleOccupationEquiv (i : Mode) : Occupation Mode ≃ Occupation Mode where
  toFun := toggleOccupation i
  invFun := toggleOccupation i
  left_inv := toggleOccupation_involutive i
  right_inv := toggleOccupation_involutive i

@[simp]
theorem toggleOccupationEquiv_apply (i : Mode) (n : Occupation Mode) :
    toggleOccupationEquiv i n = toggleOccupation i n :=
  rfl

@[simp]
theorem toggleOccupationEquiv_symm (i : Mode) :
    (toggleOccupationEquiv i).symm = toggleOccupationEquiv i :=
  rfl

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
