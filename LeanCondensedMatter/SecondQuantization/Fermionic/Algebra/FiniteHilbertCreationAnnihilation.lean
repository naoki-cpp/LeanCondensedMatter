import LeanCondensedMatter.SecondQuantization.Common.Algebra.FiniteHilbertSelfAdjoint
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.CanonicalAnticommutationRelations

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Adjointness of finite fermionic creation and annihilation operators

On a finite mode set, the occupation-subset Fock space has its canonical Euclidean Hilbert
realization. The explicit signed basis actions of `create i` and `annihilate i` are conjugate
transposes of one another. Their bounded finite-Hilbert transports are therefore genuine adjoints.

This is finite-Hilbert representation infrastructure for fermionic ladder operators. It is kept
below the thermal layer so lattice and other non-thermal models can use the bounded transports and
adjoint identities directly.
-/

namespace SecondQuantization
namespace Fermionic

noncomputable section

variable {Mode : Type*} [LinearOrder Mode]

private theorem star_matrixCoeff_create_eq_matrixCoeff_annihilate
    (i : Mode) (m n : Occupation Mode) :
    star (Common.matrixCoeff (create i) n m) =
      Common.matrixCoeff (annihilate i) m n := by
  rw [matrixCoeff_create, matrixCoeff_annihilate]
  by_cases hm : i ∈ m
  · by_cases hn : i ∈ n
    · have hne : m ≠ removeOccupation i n := by
        intro h
        have hnot : i ∉ removeOccupation i n := by
          simp [removeOccupation]
        rw [← h] at hnot
        exact hnot hm
      simp [hm, hne]
    · simp [hm, hn]
  · by_cases hn : i ∈ n
    · by_cases hnm : n = insertOccupation i m
      · subst n
        have hremove : removeOccupation i (insertOccupation i m) = m := by
          simp [removeOccupation, insertOccupation, hm]
        have hi : i ∈ insertOccupation i m := by
          simp [insertOccupation]
        rw [ite_eq_left rfl, ite_eq_right hm, hremove, ite_eq_left rfl,
          ite_eq_left hi, fermionSign_insertOccupation_of_not_lt (lt_irrefl i)]
        simp
      · have hremove : m ≠ removeOccupation i n := by
          intro hmr
          apply hnm
          rw [hmr, insertOccupation, removeOccupation, Finset.insert_erase hn]
        simp [hnm, hremove]
    · have hne : n ≠ insertOccupation i m := by
        intro h
        have hi : i ∈ insertOccupation i m := Finset.mem_insert_self i m
        rw [← h] at hi
        exact hn hi
      simp [hn, hne]

section Finite

variable [Fintype Mode]

/-- Bounded creation on the canonical finite-Hilbert fermionic Fock space. -/
noncomputable def finiteHilbertCreate (i : Mode) :
    Common.FiniteHilbertFock (Occupation Mode) →L[ℂ]
      Common.FiniteHilbertFock (Occupation Mode) :=
  Common.finiteHilbertOperatorAlgEquiv (create i)

/-- Bounded annihilation on the canonical finite-Hilbert fermionic Fock space. -/
noncomputable def finiteHilbertAnnihilate (i : Mode) :
    Common.FiniteHilbertFock (Occupation Mode) →L[ℂ]
      Common.FiniteHilbertFock (Occupation Mode) :=
  Common.finiteHilbertOperatorAlgEquiv (annihilate i)

/-- Bounded creation still obeys Pauli exclusion on the canonical finite-Hilbert occupation basis. -/
@[simp]
theorem finiteHilbertCreate_basisState_of_mem {i : Mode} {n : Occupation Mode}
    (h : i ∈ n) :
    finiteHilbertCreate i (Common.finiteHilbertBasisState n) = 0 := by
  rw [finiteHilbertCreate, Common.finiteHilbertOperator_basisState]
  change Common.finiteHilbertFockEquiv (create i (basisState n)) = 0
  rw [create_basisState_of_mem h, map_zero]

/-- Bounded creation has the same signed basis action as the algebraic occupation operator. -/
theorem finiteHilbertCreate_basisState_of_not_mem {i : Mode} {n : Occupation Mode}
    (h : i ∉ n) :
    finiteHilbertCreate i (Common.finiteHilbertBasisState n) =
      (fermionSign i n : ℂ) •
        Common.finiteHilbertBasisState (insertOccupation i n) := by
  rw [finiteHilbertCreate, Common.finiteHilbertOperator_basisState]
  change Common.finiteHilbertFockEquiv (create i (basisState n)) = _
  rw [create_basisState_of_not_mem h, map_smul]
  simp only [basisState, Common.finiteHilbertFockEquiv_basisState]

/-- Bounded annihilation vanishes on an unoccupied mode of a finite-Hilbert basis state. -/
@[simp]
theorem finiteHilbertAnnihilate_basisState_of_not_mem {i : Mode} {n : Occupation Mode}
    (h : i ∉ n) :
    finiteHilbertAnnihilate i (Common.finiteHilbertBasisState n) = 0 := by
  rw [finiteHilbertAnnihilate, Common.finiteHilbertOperator_basisState]
  change Common.finiteHilbertFockEquiv (annihilate i (basisState n)) = 0
  rw [annihilate_basisState_of_not_mem h, map_zero]

/-- Bounded annihilation has the same signed basis action as the algebraic occupation operator. -/
theorem finiteHilbertAnnihilate_basisState_of_mem {i : Mode} {n : Occupation Mode}
    (h : i ∈ n) :
    finiteHilbertAnnihilate i (Common.finiteHilbertBasisState n) =
      (fermionSign i n : ℂ) •
        Common.finiteHilbertBasisState (removeOccupation i n) := by
  rw [finiteHilbertAnnihilate, Common.finiteHilbertOperator_basisState]
  change Common.finiteHilbertFockEquiv (annihilate i (basisState n)) = _
  rw [annihilate_basisState_of_mem h, map_smul]
  simp only [basisState, Common.finiteHilbertFockEquiv_basisState]

/-- Bounded creation and annihilation are mutual Hilbert-space adjoints. -/
@[simp]
theorem star_finiteHilbertCreate (i : Mode) :
    star (finiteHilbertCreate i) = finiteHilbertAnnihilate i := by
  rw [finiteHilbertCreate, finiteHilbertAnnihilate,
    Common.star_finiteHilbertOperator_eq_iff_matrixCoeff]
  exact star_matrixCoeff_create_eq_matrixCoeff_annihilate i

/-- The reverse adjoint identity. -/
@[simp]
theorem star_finiteHilbertAnnihilate (i : Mode) :
    star (finiteHilbertAnnihilate i) = finiteHilbertCreate i := by
  have h' :
      finiteHilbertCreate i = star (finiteHilbertAnnihilate i) := by
    simpa only [star_star] using congrArg star (star_finiteHilbertCreate i)
  exact h'.symm

end Finite

end
end Fermionic
end SecondQuantization
