import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.CreationAnnihilation
import LeanCondensedMatter.SecondQuantization.Common.Algebra.DiagonalTrace
import Mathlib.Topology.Algebra.InfiniteSum.Basic

set_option linter.style.header false

/-!
# Bosonic ladder-operator diagonal-trace cyclicity

This file owns the occupation-basis reindexing needed to move one bosonic creation or annihilation
operator across `Common.tsumTrace`. The coordinate formulas and positive-occupation equivalence are
implementation details and remain private; the reusable public surface is only the two ladder
cyclicity theorems.

No Gibbs weight, energy, inverse temperature, or KMS factor enters this layer.
-/

namespace SecondQuantization
namespace Bosonic

open Common

noncomputable section

variable {Mode : Type*}

/-- File-local classical decidable equality for occupation reindexing. -/
local instance instDecidableEqLadderTraceCyclicity : DecidableEq Mode := Classical.decEq Mode

/-- Occupations with a particle available in mode `i`. -/
private def positiveOccupationSet (i : Mode) : Set (Occupation Mode) :=
  {n | n i ≠ 0}

/-- Adding one particle in mode `i` identifies all occupations with the positive-`i` subtype. -/
private noncomputable def createOccupationEquivPositive (i : Mode) :
    Occupation Mode ≃ positiveOccupationSet i where
  toFun n := ⟨createOccupation i n, by simp [positiveOccupationSet]⟩
  invFun n := removeOccupation i n.1
  left_inv n := removeOccupation_createOccupation i n
  right_inv n := by
    apply Subtype.ext
    exact createOccupation_removeOccupation_of_pos n.2

/-- Coordinate action of annihilation on an arbitrary algebraic-Fock vector. -/
private theorem annihilate_apply_coord (i : Mode) (x : FockSpace Mode) (n : Occupation Mode) :
    annihilate i x n =
      (Real.sqrt (n i + 1 : ℝ) : ℂ) * x (createOccupation i n) := by
  let evalN : FockSpace Mode →ₗ[ℂ] ℂ := Finsupp.lapply n
  let evalC : FockSpace Mode →ₗ[ℂ] ℂ := Finsupp.lapply (createOccupation i n)
  have hmap : evalN.comp (annihilate i) =
      (Real.sqrt (n i + 1 : ℝ) : ℂ) • evalC := by
    apply Common.linearMap_ext_basisState
    intro a
    simp only [LinearMap.comp_apply, LinearMap.smul_apply]
    change Common.matrixCoeff (annihilate i) n a =
      (Real.sqrt (n i + 1 : ℝ) : ℂ) * evalC (basisState a)
    rw [matrixCoeff_annihilate]
    by_cases h : a = createOccupation i n
    · subst a
      simp [evalC, basisState, Common.basisState, removeOccupation_createOccupation,
        createOccupation_apply_same]
    · by_cases ha : a i = 0
      · simp [ha, h, evalC, basisState, Common.basisState]
      · have hrem : n ≠ removeOccupation i a := by
          intro hrem
          apply h
          calc
            a = createOccupation i (removeOccupation i a) :=
              (createOccupation_removeOccupation_of_pos ha).symm
            _ = createOccupation i n := by rw [← hrem]
        simp [hrem, h, evalC, basisState, Common.basisState]
  have hx := congrArg (fun L => L x) hmap
  simpa only [evalN, evalC, LinearMap.comp_apply, LinearMap.smul_apply,
    Finsupp.lapply_apply, smul_eq_mul] using hx

/-- Coordinate action of creation on an arbitrary algebraic-Fock vector. -/
private theorem create_apply_coord (i : Mode) (x : FockSpace Mode) (n : Occupation Mode) :
    create i x n =
      (Real.sqrt (n i : ℝ) : ℂ) * x (removeOccupation i n) := by
  let evalN : FockSpace Mode →ₗ[ℂ] ℂ := Finsupp.lapply n
  let evalR : FockSpace Mode →ₗ[ℂ] ℂ := Finsupp.lapply (removeOccupation i n)
  have hmap : evalN.comp (create i) =
      (Real.sqrt (n i : ℝ) : ℂ) • evalR := by
    apply Common.linearMap_ext_basisState
    intro a
    simp only [LinearMap.comp_apply, LinearMap.smul_apply]
    change Common.matrixCoeff (create i) n a =
      (Real.sqrt (n i : ℝ) : ℂ) * evalR (basisState a)
    rw [matrixCoeff_create]
    by_cases hi : n i = 0
    · have hca : n ≠ createOccupation i a := by
        intro hca
        have hc := congrArg (fun m : Occupation Mode => m i) hca
        rw [hi, createOccupation_apply_same] at hc
        omega
      simp [hi, hca, evalR, basisState, Common.basisState]
    · by_cases h : a = removeOccupation i n
      · subst a
        have htarget : n = createOccupation i (removeOccupation i n) :=
          (createOccupation_removeOccupation_of_pos hi).symm
        have hcoord : ((removeOccupation i n) i : ℝ) + 1 = (n i : ℝ) := by
          rw [removeOccupation_apply_same, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hi)]
          push_cast
          ring
        simp [htarget, hcoord, evalR, basisState, Common.basisState]
      · have hca : n ≠ createOccupation i a := by
          intro hca
          apply h
          calc
            a = removeOccupation i (createOccupation i a) :=
              (removeOccupation_createOccupation i a).symm
            _ = removeOccupation i n := by rw [← hca]
        simp [h, hca, evalR, basisState, Common.basisState]
  have hx := congrArg (fun L => L x) hmap
  simpa only [evalN, evalR, LinearMap.comp_apply, LinearMap.smul_apply,
    Finsupp.lapply_apply, smul_eq_mul] using hx

/-- Diagonal `tsumTrace` cyclicity for one annihilation operator, proved by occupation reindexing. -/
theorem tsumTrace_annihilate_comp (i : Mode)
    (A : FockSpace Mode →ₗ[ℂ] FockSpace Mode) :
    Common.tsumTrace ((annihilate i).comp A) =
      Common.tsumTrace (A.comp (annihilate i)) := by
  let f : Occupation Mode → ℂ := fun n =>
    Common.matrixCoeff (A.comp (annihilate i)) n n
  have hpoint : ∀ n : Occupation Mode,
      Common.matrixCoeff ((annihilate i).comp A) n n = f (createOccupation i n) := by
    intro n
    unfold f Common.matrixCoeff
    change annihilate i (A (basisState n)) n =
      (A (annihilate i (basisState (createOccupation i n)))) (createOccupation i n)
    rw [annihilate_apply_coord, annihilate_basisState_of_pos]
    · rw [removeOccupation_createOccupation, createOccupation_apply_same]
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul,
        Nat.cast_add, Nat.cast_one]
    · simp [createOccupation_apply_same]
  have hsupport : Function.support f ⊆ positiveOccupationSet i := by
    intro n hn
    change n i ≠ 0
    intro hi
    apply hn
    unfold f Common.matrixCoeff
    change (A (annihilate i (basisState n))) n = 0
    rw [annihilate_basisState_of_zero hi, map_zero]
    rfl
  unfold Common.tsumTrace
  calc
    (∑' n, Common.matrixCoeff ((annihilate i).comp A) n n) =
        ∑' n, f (createOccupation i n) := tsum_congr hpoint
    _ = ∑' p : positiveOccupationSet i, f p.1 :=
      (createOccupationEquivPositive i).tsum_eq (fun p => f p.1)
    _ = ∑' n, f n := tsum_subtype_eq_of_support_subset hsupport
    _ = ∑' n, Common.matrixCoeff (A.comp (annihilate i)) n n := rfl

/-- Diagonal `tsumTrace` cyclicity for one creation operator, proved by occupation reindexing. -/
theorem tsumTrace_create_comp (i : Mode)
    (A : FockSpace Mode →ₗ[ℂ] FockSpace Mode) :
    Common.tsumTrace ((create i).comp A) =
      Common.tsumTrace (A.comp (create i)) := by
  let f : Occupation Mode → ℂ := fun n =>
    Common.matrixCoeff ((create i).comp A) n n
  have hpoint : ∀ n : Occupation Mode,
      Common.matrixCoeff (A.comp (create i)) n n = f (createOccupation i n) := by
    intro n
    unfold f Common.matrixCoeff
    change (A (create i (basisState n))) n =
      create i (A (basisState (createOccupation i n))) (createOccupation i n)
    rw [create_basisState_eq, map_smul, Finsupp.smul_apply, create_apply_coord,
      removeOccupation_createOccupation, createOccupation_apply_same]
    simp only [smul_eq_mul, Nat.cast_add, Nat.cast_one]
  have hsupport : Function.support f ⊆ positiveOccupationSet i := by
    intro n hn
    change n i ≠ 0
    intro hi
    apply hn
    unfold f Common.matrixCoeff
    change create i (A (basisState n)) n = 0
    rw [create_apply_coord, hi]
    simp
  unfold Common.tsumTrace
  calc
    (∑' n, Common.matrixCoeff ((create i).comp A) n n) = ∑' n, f n := rfl
    _ = ∑' p : positiveOccupationSet i, f p.1 :=
      (tsum_subtype_eq_of_support_subset hsupport).symm
    _ = ∑' n, f (createOccupation i n) :=
      ((createOccupationEquivPositive i).tsum_eq (fun p => f p.1)).symm
    _ = ∑' n, Common.matrixCoeff (A.comp (create i)) n n :=
      tsum_congr fun n => (hpoint n).symm

end
end Bosonic
end SecondQuantization
