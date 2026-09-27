import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.SymmDiff
import LeanCondensedMatter.SecondQuantization.Common.Algebra.OccupationBasis

set_option linter.style.header false

/-!
# Fermionic occupation-number states

Pauli exclusion means a fermionic occupation-number state is fully determined by *which* modes are
occupied — no mode can hold more than one particle — so `Occupation Mode := Finset Mode` (the set
of occupied modes), unlike the bosonic case's `Mode →₀ ℕ` in `Bosonic/Algebra/Occupation.lean`.

This file owns the fermionic occupation-number bookkeeping: the concrete vacuum and inserting,
removing, or toggling a mode in the occupied set. The statistics-independent total particle-number
grade is owned by `Common.OccupationBasis`; this module supplies the fermionic instance and its
`Finset.card` specialization. Creation and annihilation operators are defined separately in
`CreationAnnihilation.lean`, and their canonical anticommutation relations are proved in
`CanonicalAnticommutationRelations.lean`.
-/

namespace SecondQuantization
namespace Fermionic

open scoped symmDiff

variable {Mode : Type*}

/-- **Fermionic occupation-number state.** The set of occupied modes; Pauli exclusion means each
mode is either occupied (present) or empty (absent), with no multiplicity. -/
abbrev Occupation (Mode : Type*) := Finset Mode

/-- **The vacuum occupation configuration**: no mode occupied. -/
def vacuum : Occupation Mode := ∅

/-- **The fermionic occupation-basis instance**: `Occupation Mode` reads off each mode's
occupation number as `1`/`0` (occupied/empty), while the concrete configuration remains a
`Finset Mode`. The instance is noncomputable only to avoid imposing decidable equality on users
of the shared occupation-basis interface. -/
noncomputable instance occupationBasis : Common.OccupationBasis Mode (Occupation Mode) := by
  classical
  refine
    { vacuum := vacuum
      occupation := fun n i => if i ∈ n then 1 else 0
      occupation_vacuum := ?_
      finiteSupport := ?_
      ext := ?_ }
  · intro i
    simp [vacuum]
  · intro n
    exact (Finset.finite_toSet n).subset fun i hi => by
      by_contra hin
      exact hi (if_neg hin)
  · intro m n h
    exact Finset.ext fun i => by
      have hi := h i
      by_cases hm : i ∈ m <;> by_cases hn : i ∈ n <;> simp_all

/-- Fermionic spelling of the statistics-independent particle-number grade from `Common`. -/
noncomputable abbrev particleNumber (n : Occupation Mode) : ℕ :=
  Common.particleNumber (Mode := Mode) (Config := Occupation Mode) n

theorem particleNumber_eq_card (n : Occupation Mode) :
    particleNumber n = n.card := by
  classical
  change Common.particleNumber (Mode := Mode) n = n.card
  unfold Common.particleNumber
  have hs :
      (Common.OccupationBasis.finiteSupport
        (Mode := Mode) (Config := Occupation Mode) n).toFinset = n := by
    ext i
    simp only [Set.Finite.mem_toFinset]
    change ((if i ∈ n then 1 else 0) ≠ 0) ↔ i ∈ n
    by_cases hi : i ∈ n <;> simp [hi]
  rw [hs, Finset.card_eq_sum_ones]
  apply Finset.sum_congr rfl
  intro i hi
  change (if i ∈ n then 1 else 0) = 1
  simp [hi]

variable [DecidableEq Mode]

/-- **Occupying mode `i`.** Adds `i` to the occupied set; a no-op if `i` was already occupied
(Pauli exclusion — this is the set-level bookkeeping only, without the sign factor that
accompanies the actual fermionic creation operator). -/
def insertOccupation (i : Mode) (n : Occupation Mode) : Occupation Mode :=
  insert i n

/-- **Vacating mode `i`.** Removes `i` from the occupied set; a no-op if `i` was already empty. -/
def removeOccupation (i : Mode) (n : Occupation Mode) : Occupation Mode :=
  n.erase i

/-- Toggle one fermionic mode. This is symmetric difference with the singleton
mode, so the occupation bookkeeping inherits the canonical Boolean-algebra laws for finite sets. -/
def toggleOccupation (i : Mode) (n : Occupation Mode) : Occupation Mode :=
  n ∆ {i}

@[simp]
theorem mem_toggleOccupation (i : Mode) (n : Occupation Mode) :
    i ∈ toggleOccupation i n ↔ i ∉ n := by
  simp [toggleOccupation, Finset.mem_symmDiff]

@[simp]
theorem toggleOccupation_of_mem {i : Mode} {n : Occupation Mode} (h : i ∈ n) :
    toggleOccupation i n = removeOccupation i n := by
  ext j
  by_cases hj : j = i
  · subst j
    simp [toggleOccupation, Finset.mem_symmDiff, removeOccupation, h]
  · simp [toggleOccupation, Finset.mem_symmDiff, removeOccupation, hj]

@[simp]
theorem toggleOccupation_of_not_mem {i : Mode} {n : Occupation Mode} (h : i ∉ n) :
    toggleOccupation i n = insertOccupation i n := by
  ext j
  by_cases hj : j = i
  · subst j
    simp [toggleOccupation, Finset.mem_symmDiff, insertOccupation, h]
  · simp [toggleOccupation, Finset.mem_symmDiff, insertOccupation, hj]

@[simp]
theorem toggleOccupation_involutive (i : Mode) :
    Function.Involutive (toggleOccupation i) := by
  simpa [toggleOccupation] using
    (symmDiff_left_involutive ({i} : Occupation Mode))

/-- Toggling two modes commutes. -/
theorem toggleOccupation_comm (i j : Mode) (n : Occupation Mode) :
    toggleOccupation i (toggleOccupation j n) =
      toggleOccupation j (toggleOccupation i n) := by
  simpa [toggleOccupation] using
    (symmDiff_right_comm
      (a := n) (b := ({j} : Occupation Mode)) (c := ({i} : Occupation Mode)))

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
    particleNumber (insertOccupation i n) = particleNumber n + 1 := by
  simpa [particleNumber_eq_card, insertOccupation] using Finset.card_insert_of_notMem h

theorem particleNumber_insertOccupation_of_mem {i : Mode} {n : Occupation Mode}
    (h : i ∈ n) :
    particleNumber (insertOccupation i n) = particleNumber n := by
  rw [particleNumber_eq_card, particleNumber_eq_card, insertOccupation,
    Finset.insert_eq_self.2 h]

theorem particleNumber_removeOccupation_of_mem {i : Mode} {n : Occupation Mode}
    (h : i ∈ n) :
    particleNumber (removeOccupation i n) + 1 = particleNumber n := by
  simpa [particleNumber_eq_card, removeOccupation] using Finset.card_erase_add_one h

theorem particleNumber_removeOccupation_of_not_mem {i : Mode} {n : Occupation Mode}
    (h : i ∉ n) :
    particleNumber (removeOccupation i n) = particleNumber n := by
  rw [particleNumber_eq_card, particleNumber_eq_card, removeOccupation,
    Finset.erase_eq_of_notMem h]

end Fermionic
end SecondQuantization
