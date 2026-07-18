import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import LeanCondensedMatter.SecondQuantization.Common.OccupationBasis

set_option linter.style.header false

/-!
# Bosonic occupation-number states

The occupation-number representation of the bosonic Fock basis, `Occupation Mode := Mode →₀ ℕ` —
a finitely-supported function assigning each mode its number of particles. This is the preferred
basis for a future bosonic Fock space; symmetric tensor powers are deliberately avoided as the
starting point since the occupation-number picture is simpler and computationally direct. See
`Fermionic/Occupation.lean` for the fermionic counterpart (`Finset Mode`, not `Mode →₀ ℕ`, since
Pauli exclusion caps occupation at `0`/`1`) and `notes/roadmaps/second-quantization.md` for how
this fits into Track D — the fermionic, finite-mode case is now the primary line toward the
Linked Cluster Theorem, with this bosonic development kept in parallel.

This file deliberately does not assume `[Fintype Mode]`: finite support is built into `Finsupp`,
so the same API works unchanged once `Mode` is later generalized to a countably infinite mode set
(e.g. `ℕ` or a lattice `ℤ^d`). `[Fintype Mode]` only becomes relevant for later constructions that
need a *finite* mode set (e.g. an explicit finite-dimensional Fock space truncation).
-/

namespace SecondQuantization

variable {Mode : Type*}

/-- **Occupation-number state.** Assigns each mode its (finite) particle number, with finite
support. An `abbrev` rather than a `def` so that `Mode →₀ ℕ`'s existing algebraic instances
(`AddCommMonoid`, `Inhabited`, ...) transfer automatically. -/
abbrev Occupation (Mode : Type*) := Mode →₀ ℕ

/-- **The vacuum occupation configuration**: zero particles in every mode. -/
def vacuum : Occupation Mode := 0

/-- **The total particle number** of an occupation-number state, `Σᵢ n(i)`. -/
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

/-- **The single-particle occupation state** with one particle in mode `i` and none elsewhere. -/
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

/-- **Creating a particle in mode `i`**: add one particle to mode `i`, leaving all other modes
unchanged. The occupation-number counterpart of the creation operator's action on a basis state,
before creation operators themselves are defined (`CreationAnnihilation.lean`). -/
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

/-!
`removeOccupation` and the `Common.OccupationBasis` instance live under `SecondQuantization.Bosonic`
(rather than plain `SecondQuantization`, unlike the rest of this file) solely to avoid name clashes
with the fermionic `SecondQuantization.removeOccupation`/`occupationBasis` in
`Fermionic/Occupation.lean` — the fermionic line uses the plain `SecondQuantization` namespace
throughout, so any name shared between the two files must be pushed into `Bosonic` here.
-/

namespace Bosonic

/-- **The bosonic occupation-basis instance**: `Occupation Mode` reads off each mode's occupation
number directly (`n i`) — the concrete side of `Common.OccupationBasis`'s shared interface,
mirroring the fermionic line's `SecondQuantization.occupationBasis`
(`Fermionic/Occupation.lean`; the fermionic line uses the plain `SecondQuantization` namespace,
not a `Fermionic` sub-namespace). -/
instance occupationBasis : Common.OccupationBasis Mode (Occupation Mode) where
  vacuum := vacuum
  occupation n i := n i
  occupation_vacuum i := by simp [vacuum]
  finiteSupport n := (n.support.finite_toSet).subset fun i hi => Finsupp.mem_support_iff.2 hi
  ext {m n} h := Finsupp.ext h

/-- **Removing a particle from mode `i`**: subtract one particle from mode `i` (a no-op if `i`
was already unoccupied), leaving all other modes unchanged. The occupation-number counterpart of
the annihilation operator's action on a basis state, before annihilation operators themselves are
defined (`CreationAnnihilationBosonic.lean`). -/
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

/-! ## Commuting independent-mode operations

The occupation-level facts behind the CCR at distinct modes (`CCR.lean`): creating/removing at
mode `i` doesn't interact with creating/removing at a different mode `j`. -/

theorem createOccupation_comm (i j : Mode) (n : Occupation Mode) :
    createOccupation i (createOccupation j n) = createOccupation j (createOccupation i n) := by
  simp only [createOccupation]
  exact add_right_comm n (singleOccupation j) (singleOccupation i)

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
end SecondQuantization
