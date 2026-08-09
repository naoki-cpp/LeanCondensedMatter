import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.FreeFirstPair
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.MatrixEvaluation
import LeanCondensedMatter.Combinatorics.FiniteIndex.EraseIdxOfFn

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Concrete free-boson Gibbs permanent evaluation

For the number-conserving free thermal state, creator--creator and annihilator--annihilator
contractions vanish.  Normal-ordered moments therefore satisfy the permanent first-row recurrence.
This file derives that recurrence directly from CCR peel plus KMS rotation and identifies the result
with Mathlib's `Matrix.permanent` through the common matrix backend.

The explicit perfect-pairing expansion is intentionally not a second public endpoint here.  General
Gaussian pairing evaluation will later be represented by a Hafnian, while `Pairing` remains the
combinatorial data structure used by diagrammatics.
-/

namespace SecondQuantization
namespace Bosonic

open Common

noncomputable section

variable {Mode : Type*} [Fintype Mode]

/-- File-local classical decidable equality for the concrete thermal kernel. -/
local instance instDecidableEqConcreteExpectationRecursion : DecidableEq Mode := Classical.decEq Mode

namespace FreeThermalField

/-- The normal-ordered number-conserving field list: all creators followed by all annihilators. -/
def normalOrderedFields {n : ℕ} (createMode annihilateMode : Fin n → Mode) :
    List (FreeThermalField Mode) :=
  List.ofFn (fun i => .create (createMode i)) ++
    List.ofFn (fun i => .annihilate (annihilateMode i))

@[simp]
theorem normalOrderedFields_zero
    (createMode annihilateMode : Fin 0 → Mode) :
    normalOrderedFields createMode annihilateMode = [] := by
  simp [normalOrderedFields]

/-- Normal-ordered free-Gibbs moment for equally many creators and annihilators. -/
noncomputable def freeGibbsNormalOrderedMoment
    (ε : Mode → ℝ) (β : ℝ) {n : ℕ}
    (createMode annihilateMode : Fin n → Mode) : ℂ :=
  freeGibbsExpectation ε β (orderedProduct (normalOrderedFields createMode annihilateMode))

@[simp]
theorem freeGibbsNormalOrderedMoment_zero
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (createMode annihilateMode : Fin 0 → Mode) :
    freeGibbsNormalOrderedMoment ε β createMode annihilateMode = 1 := by
  simp [freeGibbsNormalOrderedMoment, normalOrderedFields,
    orderedProduct, freeGibbsExpectation_id ε β hpos]

/-- The concrete normal-ordered bosonic Gibbs moment obeys the permanent first-row recurrence. -/
theorem freeGibbsNormalOrderedMoment_succ
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (n : ℕ) (createMode annihilateMode : Fin (n + 1) → Mode) :
    freeGibbsNormalOrderedMoment ε β createMode annihilateMode =
      ∑ j : Fin (n + 1),
        freeThermalPairValue ε β (.create (createMode 0)) (.annihilate (annihilateMode j)) *
          freeGibbsNormalOrderedMoment ε β
            (fun i : Fin n => createMode i.succ)
            (fun i : Fin n => annihilateMode (j.succAbove i)) := by
  unfold freeGibbsNormalOrderedMoment normalOrderedFields
  rw [List.ofFn_succ]
  let creators : List (FreeThermalField Mode) :=
    List.ofFn (fun i : Fin n => .create (createMode i.succ))
  let annihilators : List (FreeThermalField Mode) :=
    List.ofFn (fun j : Fin (n + 1) => .annihilate (annihilateMode j))
  change freeGibbsExpectation ε β
      (orderedProduct (.create (createMode 0) :: (creators ++ annihilators))) = _
  rw [freeGibbsExpectation_cons_eq_kmsRatio_mul_operatorPeelSum ε β hpos,
    freeGibbsExpectation_operatorPeelSum_eq_sum ε β hpos, Finset.mul_sum]
  have hlen : (creators ++ annihilators).length = n + (n + 1) := by
    simp [creators, annihilators]
  let e : Fin ((creators ++ annihilators).length) ≃ Fin (n + (n + 1)) :=
    Fin.castIso hlen
  rw [Fintype.sum_equiv e
    (fun k : Fin ((creators ++ annihilators).length) =>
      ((FreeThermalField.create (createMode 0)).kmsFactor ε β /
        ((FreeThermalField.create (createMode 0)).kmsFactor ε β - 1)) *
        ((FreeThermalField.create (createMode 0)).exchangeValue
            ((creators ++ annihilators)[(k : ℕ)]'k.isLt) *
          freeGibbsExpectation ε β (orderedProduct ((creators ++ annihilators).eraseIdx k)))
    (fun k : Fin (n + (n + 1)) =>
      ((FreeThermalField.create (createMode 0)).kmsFactor ε β /
        ((FreeThermalField.create (createMode 0)).kmsFactor ε β - 1)) *
        ((FreeThermalField.create (createMode 0)).exchangeValue
            ((creators ++ annihilators)[(e.symm k : ℕ)]'(e.symm k).isLt) *
          freeGibbsExpectation ε β
            (orderedProduct ((creators ++ annihilators).eraseIdx (e.symm k))))
    (fun k => rfl)]
  rw [Fin.sum_univ_add]
  have hcreate :
      (∑ i : Fin n,
        ((FreeThermalField.create (createMode 0)).kmsFactor ε β /
          ((FreeThermalField.create (createMode 0)).kmsFactor ε β - 1)) *
          ((FreeThermalField.create (createMode 0)).exchangeValue
              ((creators ++ annihilators)[(e.symm (Fin.castAdd (n + 1) i) : ℕ)]'
                (e.symm (Fin.castAdd (n + 1) i)).isLt) *
            freeGibbsExpectation ε β
              (orderedProduct
                ((creators ++ annihilators).eraseIdx
                  (e.symm (Fin.castAdd (n + 1) i)))))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp [e, creators, annihilators, FreeThermalField.exchangeValue]
  rw [hcreate, zero_add]
  apply Finset.sum_congr rfl
  intro j _
  have hpair := kmsRatio_mul_exchangeValue_eq_freeThermalPairValue
    ε β hpos (.create (createMode 0)) (.annihilate (annihilateMode j))
  rw [← hpair]
  simp [e, creators, annihilators, normalOrderedFields,
    List.eraseIdx_ofFn_eq_ofFn_succAbove]

/-- Concrete free-boson Bloch--de Dominicis evaluation in the number-conserving sector: the
normal-ordered Gibbs moment is the permanent of the thermal creator--annihilator contraction
matrix. -/
theorem freeGibbsNormalOrderedMoment_eq_permanent
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (n : ℕ) (createMode annihilateMode : Fin n → Mode) :
    freeGibbsNormalOrderedMoment ε β createMode annihilateMode =
      Common.BlochDeDominicis.permanentBipartitePairValue
        (fun i j => freeThermalPairValue ε β (.create i) (.annihilate j))
        createMode annihilateMode := by
  exact Common.BlochDeDominicis.moment_eq_permanentBipartitePairValue_of_recursion
    (fun i j => freeThermalPairValue ε β (.create i) (.annihilate j))
    (fun n createMode annihilateMode =>
      freeGibbsNormalOrderedMoment ε β createMode annihilateMode)
    (fun createMode annihilateMode =>
      freeGibbsNormalOrderedMoment_zero ε β hpos createMode annihilateMode)
    (fun n createMode annihilateMode =>
      freeGibbsNormalOrderedMoment_succ ε β hpos n createMode annihilateMode)
    n createMode annihilateMode

end FreeThermalField

end
end Bosonic
end SecondQuantization
