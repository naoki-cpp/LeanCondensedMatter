import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteHilbertSelfAdjoint
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.CanonicalAnticommutationRelations

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Adjointness of finite fermionic creation and annihilation operators

On a finite mode set, the occupation-subset Fock space has its canonical Euclidean Hilbert
realization. The explicit signed basis actions of `create i` and `annihilate i` are conjugate
transposes of one another. Their bounded finite-Hilbert transports are therefore genuine adjoints.

This result is the analytic bridge needed to prove self-adjointness of number-conserving one-body
Hamiltonians and currents from Hermitian hopping coefficients.
-/

namespace SecondQuantization
namespace Fermionic

noncomputable section

variable {Mode : Type*} [Fintype Mode] [LinearOrder Mode]

/-- The creation and annihilation coordinate matrices are conjugate transposes. -/
theorem star_matrixCoeff_create_eq_matrixCoeff_annihilate
    (i : Mode) (m n : Occupation Mode) :
    star (Common.matrixCoeff (create i) n m) =
      Common.matrixCoeff (annihilate i) m n := by
  unfold Common.matrixCoeff
  change star ((create i) (basisState m) n) =
    (annihilate i) (basisState n) m
  by_cases hm : i ∈ m
  · rw [create_basisState_of_mem hm]
    simp only [LinearMap.zero_apply, star_zero]
    by_cases hn : i ∈ n
    · rw [annihilate_basisState_of_mem hn]
      have hne : removeOccupation i n ≠ m := by
        intro h
        have hnot : i ∉ removeOccupation i n := Finset.notMem_erase i n
        rw [h] at hnot
        exact hnot hm
      simp [basisState, Common.basisState, hne]
    · rw [annihilate_basisState_of_not_mem hn]
      rfl
  · rw [create_basisState_of_not_mem hm]
    by_cases hn : i ∈ n
    · rw [annihilate_basisState_of_mem hn]
      by_cases hnm : n = insertOccupation i m
      · subst n
        have hremove : removeOccupation i (insertOccupation i m) = m := by
          simp [removeOccupation, insertOccupation, hm]
        rw [hremove, fermionSign_insertOccupation_of_not_lt hm (lt_irrefl i)]
        simp [basisState, Common.basisState]
      · have hinsert : insertOccupation i m ≠ n := Ne.symm hnm
        have hremove : removeOccupation i n ≠ m := by
          intro h
          have hins : insertOccupation i (removeOccupation i n) = n := by
            rw [insertOccupation, removeOccupation, Finset.insert_erase hn]
          rw [h] at hins
          exact hnm hins.symm
        simp [basisState, Common.basisState, hinsert, hremove]
    · rw [annihilate_basisState_of_not_mem hn]
      have hne : insertOccupation i m ≠ n := by
        intro h
        have hi : i ∈ insertOccupation i m := Finset.mem_insert_self i m
        rw [h] at hi
        exact hn hi
      simp [basisState, Common.basisState, hne]

/-- Bounded creation on the canonical finite-Hilbert fermionic Fock space. -/
noncomputable def finiteHilbertCreate (i : Mode) :
    Common.FiniteHilbertFock (Occupation Mode) →L[ℂ]
      Common.FiniteHilbertFock (Occupation Mode) :=
  Common.finiteHilbertOperator (create i)

/-- Bounded annihilation on the canonical finite-Hilbert fermionic Fock space. -/
noncomputable def finiteHilbertAnnihilate (i : Mode) :
    Common.FiniteHilbertFock (Occupation Mode) →L[ℂ]
      Common.FiniteHilbertFock (Occupation Mode) :=
  Common.finiteHilbertOperator (annihilate i)

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
  rw [← star_finiteHilbertCreate i]
  simp

end
end Fermionic
end SecondQuantization
