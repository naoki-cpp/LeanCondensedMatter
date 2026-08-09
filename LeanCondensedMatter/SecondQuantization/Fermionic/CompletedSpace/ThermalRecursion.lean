import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.ThermalFirstPair
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.ThermalPeelIndexed
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.MatrixEvaluation

set_option linter.style.header false

/-!
# Completed fermionic Gibbs determinant evaluation

In the number-conserving free fermion state, same-type contractions vanish.  A normal-ordered moment
therefore reduces to a determinant of creator--annihilator two-point functions.  The only extra
factor is the fixed sign required to move the annihilator block through the creator block.

This file derives the specialized recurrence directly from the completed CAR peel and KMS rotation
and uses Mathlib's determinant Laplace expansion through the common matrix backend.  It deliberately
does not expose a parallel perfect-pairing evaluation endpoint.
-/

namespace SecondQuantization
namespace Fermionic

open QuantumTheory

noncomputable section

variable {Mode : Type*} [LinearOrder Mode]

namespace CompletedThermalLadder

/-- The normal-ordered number-conserving ladder list: all creators followed by all annihilators. -/
def normalOrderedLadders {n : ℕ} (createMode annihilateMode : Fin n → Mode) :
    List (CompletedThermalLadder Mode) :=
  List.ofFn (fun i => .create (createMode i)) ++
    List.ofFn (fun i => .annihilate (annihilateMode i))

@[simp]
theorem normalOrderedLadders_zero
    (createMode annihilateMode : Fin 0 → Mode) :
    normalOrderedLadders createMode annihilateMode = [] := by
  simp [normalOrderedLadders]

/-- Normal-ordered completed free-Gibbs moment. -/
noncomputable def completedFreeGibbsNormalOrderedMoment
    (ε : Mode → ℝ) (β : ℝ) (hsum : CompletedFreeGibbsSummable ε β) {n : ℕ}
    (createMode annihilateMode : Fin n → Mode) : ℂ :=
  completedFreeGibbsExpectation ε β hsum (normalOrderedLadders createMode annihilateMode)

/-- Admissibility needed while recursively peeling creators. -/
def completedFreeGibbsNormalOrderAdmissible
    (ε : Mode → ℝ) (β : ℝ) {n : ℕ} (createMode : Fin n → Mode) : Prop :=
  ∀ i, (1 : ℂ) + (.create (createMode i) : CompletedThermalLadder Mode).gibbsFactor ε β ≠ 0

@[simp]
theorem completedFreeGibbsNormalOrderedMoment_zero
    (ε : Mode → ℝ) (β : ℝ) (hsum : CompletedFreeGibbsSummable ε β)
    (createMode annihilateMode : Fin 0 → Mode) :
    completedFreeGibbsNormalOrderedMoment ε β hsum createMode annihilateMode = 1 := by
  simp [completedFreeGibbsNormalOrderedMoment, normalOrderedLadders,
    completedFreeGibbsExpectation_nil ε β hsum]

/-- Sign of the creator-first normal-order convention relative to determinant column order. -/
def fermionNormalOrderSign : ℕ → ℂ
  | 0 => 1
  | n + 1 => (-1 : ℂ) ^ n * fermionNormalOrderSign n

@[simp]
theorem fermionNormalOrderSign_zero : fermionNormalOrderSign 0 = 1 := rfl

@[simp]
theorem fermionNormalOrderSign_succ (n : ℕ) :
    fermionNormalOrderSign (n + 1) = (-1 : ℂ) ^ n * fermionNormalOrderSign n := rfl

/-- The completed normal-ordered fermionic Gibbs moment obeys determinant recurrence, with the
fixed block-order sign `(-1)^n` produced when the leading creator reaches the annihilator block. -/
theorem completedFreeGibbsNormalOrderedMoment_succ
    (ε : Mode → ℝ) (β : ℝ) (hsum : CompletedFreeGibbsSummable ε β)
    (n : ℕ) (createMode annihilateMode : Fin (n + 1) → Mode)
    (hcreate : completedFreeGibbsNormalOrderAdmissible ε β createMode) :
    completedFreeGibbsNormalOrderedMoment ε β hsum createMode annihilateMode =
      (-1 : ℂ) ^ n *
        ∑ j : Fin (n + 1),
          (-1 : ℂ) ^ (j : ℕ) *
            completedFreeGibbsExpectation ε β hsum
              [.create (createMode 0), .annihilate (annihilateMode j)] *
            completedFreeGibbsNormalOrderedMoment ε β hsum
              (fun i : Fin n => createMode i.succ)
              (fun i : Fin n => annihilateMode (j.succAbove i)) := by
  unfold completedFreeGibbsNormalOrderedMoment normalOrderedLadders
  rw [List.ofFn_succ]
  let creators : List (CompletedThermalLadder Mode) :=
    List.ofFn (fun i : Fin n => .create (createMode i.succ))
  let annihilators : List (CompletedThermalLadder Mode) :=
    List.ofFn (fun j : Fin (n + 1) => .annihilate (annihilateMode j))
  change completedFreeGibbsExpectation ε β hsum
      (.create (createMode 0) :: (creators ++ annihilators)) = _
  have hlen : (creators ++ annihilators).length = 2 * n + 1 := by
    simp [creators, annihilators]
    omega
  rw [completedFreeGibbsExpectation_cons_eq_gibbsRatio_mul_peel
    ε β hsum n (.create (createMode 0)) (creators ++ annihilators) hlen (hcreate 0),
    completedFreeGibbsExpectation_thermalPeelSum_eq_sum, Finset.mul_sum]
  have hlen' : (creators ++ annihilators).length = n + (n + 1) := by
    simp [creators, annihilators]
  let e : Fin ((creators ++ annihilators).length) ≃ Fin (n + (n + 1)) :=
    Fin.castIso hlen'
  rw [Fintype.sum_equiv e
    (fun k : Fin ((creators ++ annihilators).length) =>
      ((.create (createMode 0) : CompletedThermalLadder Mode).gibbsFactor ε β /
        ((1 : ℂ) + (.create (createMode 0) : CompletedThermalLadder Mode).gibbsFactor ε β)) *
        (((-1 : ℂ) ^ (k : ℕ)) *
          (.create (createMode 0) : CompletedThermalLadder Mode).anticommutatorValue
            ((creators ++ annihilators)[(k : ℕ)]'k.isLt) *
          completedFreeGibbsExpectation ε β hsum ((creators ++ annihilators).eraseIdx k)))
    (fun k : Fin (n + (n + 1)) =>
      ((.create (createMode 0) : CompletedThermalLadder Mode).gibbsFactor ε β /
        ((1 : ℂ) + (.create (createMode 0) : CompletedThermalLadder Mode).gibbsFactor ε β)) *
        (((-1 : ℂ) ^ (e.symm k : ℕ)) *
          (.create (createMode 0) : CompletedThermalLadder Mode).anticommutatorValue
            ((creators ++ annihilators)[(e.symm k : ℕ)]'(e.symm k).isLt) *
          completedFreeGibbsExpectation ε β hsum
            ((creators ++ annihilators).eraseIdx (e.symm k))))
    (fun k => rfl)]
  rw [Fin.sum_univ_add]
  have hcreator :
      (∑ i : Fin n,
        ((.create (createMode 0) : CompletedThermalLadder Mode).gibbsFactor ε β /
          ((1 : ℂ) + (.create (createMode 0) : CompletedThermalLadder Mode).gibbsFactor ε β)) *
          (((-1 : ℂ) ^ (e.symm (Fin.castAdd (n + 1) i) : ℕ)) *
            (.create (createMode 0) : CompletedThermalLadder Mode).anticommutatorValue
              ((creators ++ annihilators)
                [(e.symm (Fin.castAdd (n + 1) i) : ℕ)]'
                (e.symm (Fin.castAdd (n + 1) i)).isLt) *
            completedFreeGibbsExpectation ε β hsum
              ((creators ++ annihilators).eraseIdx
                (e.symm (Fin.castAdd (n + 1) i)))))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp [e, creators, annihilators, CompletedThermalLadder.anticommutatorValue]
  rw [hcreator, zero_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hpair := completedFreeGibbsExpectation_pair_eq
    ε β hsum (.create (createMode 0)) (.annihilate (annihilateMode j)) (hcreate 0)
  rw [hpair]
  simp [e, creators, annihilators, normalOrderedLadders,
    List.eraseIdx_ofFn_eq_ofFn_succAbove, pow_add]
  ring

/-- Completed free-fermion Bloch--de Dominicis evaluation in the number-conserving normal-ordered
sector.  The Gibbs moment is the determinant of the creator--annihilator two-point matrix times the
fixed normal-order sign. -/
theorem completedFreeGibbsNormalOrderedMoment_eq_determinant
    (ε : Mode → ℝ) (β : ℝ) (hsum : CompletedFreeGibbsSummable ε β)
    (n : ℕ) (createMode annihilateMode : Fin n → Mode)
    (hcreate : completedFreeGibbsNormalOrderAdmissible ε β createMode) :
    completedFreeGibbsNormalOrderedMoment ε β hsum createMode annihilateMode =
      fermionNormalOrderSign n *
        Common.BlochDeDominicis.determinantBipartitePairValue
          (fun i j => completedFreeGibbsExpectation ε β hsum [.create i, .annihilate j])
          createMode annihilateMode := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [completedFreeGibbsNormalOrderedMoment_succ ε β hsum n createMode annihilateMode hcreate]
      have htail : completedFreeGibbsNormalOrderAdmissible ε β
          (fun i : Fin n => createMode i.succ) := fun i => hcreate i.succ
      simp_rw [ih (fun i : Fin n => createMode i.succ)
        (fun i : Fin n => annihilateMode (·.succAbove i)) htail]
      rw [Common.BlochDeDominicis.determinantBipartitePairValue_succ]
      simp only [fermionNormalOrderSign_succ]
      ring

end CompletedThermalLadder

end
end Fermionic
end SecondQuantization
