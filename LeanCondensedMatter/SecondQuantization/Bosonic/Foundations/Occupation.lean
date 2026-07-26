import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import LeanCondensedMatter.SecondQuantization.Common.OccupationBasis

set_option linter.style.header false

/-!
# Bosonic occupation-number states

A bosonic occupation state is a finitely supported function `Mode →₀ ℕ`. The support is finite even
when the mode type is not, so the bookkeeping layer does not require `[Fintype Mode]`.

The canonical API lives in `SecondQuantization.Bosonic`. Compatibility aliases for the older
`SecondQuantization`-level names are retained at the end of the file.
-/

namespace SecondQuantization
namespace Bosonic

variable {Mode : Type*}

/-- A finitely supported bosonic occupation-number state. -/
abbrev Occupation (Mode : Type*) := Mode →₀ ℕ

/-- The zero-particle occupation configuration. -/
def vacuum : Occupation Mode := 0

/-- The total particle number `Σᵢ n(i)`. -/
def particleNumber (n : Occupation Mode) : ℕ := n.sum fun _ k => k

@[simp]
theorem particleNumber_zero : particleNumber (0 : Occupation Mode) = 0 := by
  simp [particleNumber]

@[simp]
theorem particleNumber_vacuum : particleNumber (vacuum : Occupation Mode) = 0 :=
  particleNumber_zero

theorem particleNumber_add (m n : Occupation Mode) :
    particleNumber (m + n) = particleNumber m + particleNumber n :=
  Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

/-- The occupation state with one particle in mode `i`. -/
noncomputable def singleOccupation (i : Mode) : Occupation Mode := Finsupp.single i 1

@[simp]
theorem singleOccupation_apply_same (i : Mode) : singleOccupation i i = 1 :=
  Finsupp.single_eq_same

@[simp]
theorem singleOccupation_apply_ne {i j : Mode} (h : j ≠ i) : singleOccupation i j = 0 :=
  Finsupp.single_eq_of_ne h

@[simp]
theorem particleNumber_singleOccupation (i : Mode) :
    particleNumber (singleOccupation i : Occupation Mode) = 1 := by
  simp [particleNumber, singleOccupation]

/-- Add one particle in mode `i`. -/
noncomputable def createOccupation (i : Mode) (n : Occupation Mode) : Occupation Mode :=
  n + singleOccupation i

@[simp]
theorem particleNumber_createOccupation (i : Mode) (n : Occupation Mode) :
    particleNumber (createOccupation i n) = particleNumber n + 1 := by
  rw [createOccupation, particleNumber_add, particleNumber_singleOccupation]

@[simp]
theorem createOccupation_apply_same (i : Mode) (n : Occupation Mode) :
    createOccupation i n i = n i + 1 := by
  simp [createOccupation, singleOccupation]

theorem createOccupation_apply_ne {i j : Mode} (h : j ≠ i) (n : Occupation Mode) :
    createOccupation i n j = n j := by
  simp [createOccupation, singleOccupation, h]

/-- The shared occupation-basis interface for bosonic occupation states. -/
instance occupationBasis : Common.OccupationBasis Mode (Occupation Mode) where
  vacuum := vacuum
  occupation n i := n i
  occupation_vacuum i := by simp [vacuum]
  finiteSupport n := (n.support.finite_toSet).subset fun i hi => Finsupp.mem_support_iff.2 hi
  ext {m n} h := Finsupp.ext h

/-- Remove one particle from mode `i`, with zero left unchanged. -/
noncomputable def removeOccupation (i : Mode) (n : Occupation Mode) : Occupation Mode :=
  n.update i (n i - 1)

@[simp]
theorem removeOccupation_apply_same (i : Mode) (n : Occupation Mode) :
    removeOccupation i n i = n i - 1 := by
  classical
  simp [removeOccupation, Finsupp.update_apply]

theorem removeOccupation_apply_ne {i j : Mode} (h : j ≠ i) (n : Occupation Mode) :
    removeOccupation i n j = n j := by
  classical
  simp [removeOccupation, Finsupp.update_apply, h]

theorem createOccupation_removeOccupation_of_pos {i : Mode} {n : Occupation Mode} (h : n i ≠ 0) :
    createOccupation i (removeOccupation i n) = n := by
  ext j
  rcases eq_or_ne j i with rfl | hj
  · rw [createOccupation_apply_same, removeOccupation_apply_same]; omega
  · rw [createOccupation_apply_ne hj, removeOccupation_apply_ne hj]

theorem removeOccupation_createOccupation (i : Mode) (n : Occupation Mode) :
    removeOccupation i (createOccupation i n) = n := by
  ext j
  rcases eq_or_ne j i with rfl | hj
  · rw [removeOccupation_apply_same, createOccupation_apply_same]; omega
  · rw [removeOccupation_apply_ne hj, createOccupation_apply_ne hj]

theorem particleNumber_removeOccupation_of_pos {i : Mode} {n : Occupation Mode} (h : n i ≠ 0) :
    particleNumber (removeOccupation i n) + 1 = particleNumber n := by
  conv_rhs => rw [← createOccupation_removeOccupation_of_pos h]
  rw [particleNumber_createOccupation]

/-- Creating particles in two modes commutes. -/
theorem createOccupation_comm (i j : Mode) (n : Occupation Mode) :
    createOccupation i (createOccupation j n) = createOccupation j (createOccupation i n) := by
  simp only [createOccupation]
  exact add_right_comm n (singleOccupation j) (singleOccupation i)

/-- Removing particles in distinct modes commutes. -/
theorem removeOccupation_comm {i j : Mode} (h : i ≠ j) (n : Occupation Mode) :
    removeOccupation i (removeOccupation j n) = removeOccupation j (removeOccupation i n) := by
  ext k
  rcases eq_or_ne k i with rfl | hki
  · rw [removeOccupation_apply_same, removeOccupation_apply_ne h,
      removeOccupation_apply_ne h, removeOccupation_apply_same]
  · rcases eq_or_ne k j with rfl | hkj
    · rw [removeOccupation_apply_ne (Ne.symm h), removeOccupation_apply_same,
        removeOccupation_apply_same, removeOccupation_apply_ne (Ne.symm h)]
    · rw [removeOccupation_apply_ne hki, removeOccupation_apply_ne hkj,
        removeOccupation_apply_ne hkj, removeOccupation_apply_ne hki]

/-- Creation and removal in distinct modes commute. -/
theorem removeOccupation_createOccupation_of_ne {i j : Mode} (h : i ≠ j) (n : Occupation Mode) :
    removeOccupation i (createOccupation j n) = createOccupation j (removeOccupation i n) := by
  ext k
  rcases eq_or_ne k i with rfl | hki
  · rw [removeOccupation_apply_same, createOccupation_apply_ne h,
      createOccupation_apply_ne h, removeOccupation_apply_same]
  · rcases eq_or_ne k j with rfl | hkj
    · rw [removeOccupation_apply_ne (Ne.symm h), createOccupation_apply_same,
        createOccupation_apply_same, removeOccupation_apply_ne (Ne.symm h)]
    · rw [removeOccupation_apply_ne hki, createOccupation_apply_ne hkj,
        createOccupation_apply_ne hkj, removeOccupation_apply_ne hki]

end Bosonic

/-! ## Compatibility aliases

These preserve the original `SecondQuantization`-level occupation API while new code uses the
`SecondQuantization.Bosonic` namespace.
-/

variable {Mode : Type*}

abbrev Occupation (Mode : Type*) := Bosonic.Occupation Mode
abbrev vacuum : Occupation Mode := Bosonic.vacuum
abbrev particleNumber (n : Occupation Mode) : ℕ := Bosonic.particleNumber n

@[simp]
theorem particleNumber_zero : particleNumber (0 : Occupation Mode) = 0 :=
  Bosonic.particleNumber_zero

@[simp]
theorem particleNumber_vacuum : particleNumber (vacuum : Occupation Mode) = 0 :=
  Bosonic.particleNumber_vacuum

theorem particleNumber_add (m n : Occupation Mode) :
    particleNumber (m + n) = particleNumber m + particleNumber n :=
  Bosonic.particleNumber_add m n

noncomputable abbrev singleOccupation (i : Mode) : Occupation Mode :=
  Bosonic.singleOccupation i

@[simp]
theorem singleOccupation_apply_same (i : Mode) : singleOccupation i i = 1 :=
  Bosonic.singleOccupation_apply_same i

@[simp]
theorem singleOccupation_apply_ne {i j : Mode} (h : j ≠ i) : singleOccupation i j = 0 :=
  Bosonic.singleOccupation_apply_ne h

@[simp]
theorem particleNumber_singleOccupation (i : Mode) :
    particleNumber (singleOccupation i : Occupation Mode) = 1 :=
  Bosonic.particleNumber_singleOccupation i

noncomputable abbrev createOccupation (i : Mode) (n : Occupation Mode) : Occupation Mode :=
  Bosonic.createOccupation i n

@[simp]
theorem particleNumber_createOccupation (i : Mode) (n : Occupation Mode) :
    particleNumber (createOccupation i n) = particleNumber n + 1 :=
  Bosonic.particleNumber_createOccupation i n

@[simp]
theorem createOccupation_apply_same (i : Mode) (n : Occupation Mode) :
    createOccupation i n i = n i + 1 :=
  Bosonic.createOccupation_apply_same i n

theorem createOccupation_apply_ne {i j : Mode} (h : j ≠ i) (n : Occupation Mode) :
    createOccupation i n j = n j :=
  Bosonic.createOccupation_apply_ne h n

end SecondQuantization
