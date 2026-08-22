import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.ThermalPeel

set_option linter.style.header false

/-!
# Completed free-Gibbs KMS rotation

This file proves the cyclic thermal rotation needed to close the completed fermionic peel identity.
The proof stays inside the canonical occupation representation: the Gibbs expectation is expanded as
its absolutely convergent occupation-basis series and reindexed by the one-mode occupation toggle.
No general trace-cyclicity theorem and no formal exponential of the unbounded Hamiltonian are used.
-/

namespace SecondQuantization
namespace Fermionic

open QuantumTheory

noncomputable section

variable {Mode : Type*} [LinearOrder Mode]

namespace CompletedThermalLadder

/-- Completed free-Gibbs KMS rotation for one thermal ladder and an arbitrary bounded operator:
`⟨C A⟩β = gβ(C) ⟨A C⟩β`.  The scalar `gβ(C)` is the same factor appearing in
`ρβ C = gβ(C) C ρβ`. -/
theorem completedFreeGibbsExpectation_operator_comp
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β)
    (C : CompletedThermalLadder Mode)
    (A : CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode) :
    (purePointGibbsDensityOperator completedOccupationHilbertBasis
      (fermionEnergy ε) β hsum).expectation (C.operator.comp A) =
      C.gibbsFactor ε β *
        (purePointGibbsDensityOperator completedOccupationHilbertBasis
          (fermionEnergy ε) β hsum).expectation (A.comp C.operator) := by
  rw [completedFreeGibbsDensityOperator_expectation_eq_tsum,
    completedFreeGibbsDensityOperator_expectation_eq_tsum, ← tsum_mul_left]
  cases C with
  | create i =>
      simp only [operator_create, gibbsFactor_create]
      let f : Occupation Mode → ℂ := fun n =>
        Complex.exp (-(β : ℂ) * (ε i : ℂ)) *
          ((purePointGibbsProbability (fermionEnergy ε) β n : ℂ) *
            inner ℂ (completedBasisState n)
              ((A.comp (completedCreate i)) (completedBasisState n)))
      calc
        (∑' n : Occupation Mode,
            (purePointGibbsProbability (fermionEnergy ε) β n : ℂ) *
              inner ℂ (completedBasisState n)
                (((completedCreate i).comp A) (completedBasisState n))) =
            ∑' n : Occupation Mode, f (toggleOccupation i n) := by
          apply tsum_congr
          intro n
          by_cases hi : i ∈ n
          · have hremove : i ∉ removeOccupation i n := by
              simp [removeOccupation]
            have hrestore : insertOccupation i (removeOccupation i n) = n := by
              simpa [insertOccupation, removeOccupation] using Finset.insert_erase hi
            dsimp [f]
            rw [inner_completedBasisState_left, completedCreate_apply, if_pos hi,
              toggleOccupation_of_mem hi,
              coe_completedFreeGibbsProbability_removeOccupation_of_mem ε β hi,
              completedCreate_basisState_of_not_mem hremove, map_smul, inner_smul_right,
              inner_completedBasisState_left, hrestore]
            have hexp :
                Complex.exp (-(β : ℂ) * (ε i : ℂ)) *
                    Complex.exp ((β : ℂ) * (ε i : ℂ)) = 1 := by
              rw [← Complex.exp_add]
              ring_nf
              exact Complex.exp_zero
            calc
              _ = 1 * ((purePointGibbsProbability (fermionEnergy ε) β n : ℂ) *
                  (fermionPhase i (removeOccupation i n) *
                    (A (completedBasisState n)) (removeOccupation i n))) := by ring
              _ = (Complex.exp (-(β : ℂ) * (ε i : ℂ)) *
                    Complex.exp ((β : ℂ) * (ε i : ℂ))) *
                    ((purePointGibbsProbability (fermionEnergy ε) β n : ℂ) *
                      (fermionPhase i (removeOccupation i n) *
                        (A (completedBasisState n)) (removeOccupation i n))) := by
                    rw [hexp]
              _ = _ := by ring
          · have hit : i ∈ toggleOccupation i n :=
              (mem_toggleOccupation i n).mpr hi
            dsimp [f]
            rw [inner_completedBasisState_left, completedCreate_apply, if_neg hi,
              completedCreate_basisState_of_mem hit, map_zero, inner_zero_right]
            ring
        _ = ∑' n : Occupation Mode, f n := by
          simpa [toggleOccupationEquiv_apply] using
            (Equiv.tsum_eq (toggleOccupationEquiv i) f)
        _ = ∑' n : Occupation Mode,
            Complex.exp (-(β : ℂ) * (ε i : ℂ)) *
              ((purePointGibbsProbability (fermionEnergy ε) β n : ℂ) *
                inner ℂ (completedBasisState n)
                  ((A.comp (completedCreate i)) (completedBasisState n))) := by
          rfl
  | annihilate i =>
      simp only [operator_annihilate, gibbsFactor_annihilate]
      let f : Occupation Mode → ℂ := fun n =>
        Complex.exp ((β : ℂ) * (ε i : ℂ)) *
          ((purePointGibbsProbability (fermionEnergy ε) β n : ℂ) *
            inner ℂ (completedBasisState n)
              ((A.comp (completedAnnihilate i)) (completedBasisState n)))
      calc
        (∑' n : Occupation Mode,
            (purePointGibbsProbability (fermionEnergy ε) β n : ℂ) *
              inner ℂ (completedBasisState n)
                (((completedAnnihilate i).comp A) (completedBasisState n))) =
            ∑' n : Occupation Mode, f (toggleOccupation i n) := by
          apply tsum_congr
          intro n
          by_cases hi : i ∈ n
          · have hit : i ∉ toggleOccupation i n := by
              intro hit
              exact ((mem_toggleOccupation i n).mp hit) hi
            dsimp [f]
            rw [inner_completedBasisState_left, completedAnnihilate_apply, if_pos hi,
              completedAnnihilate_basisState_of_not_mem hit, map_zero, inner_zero_right]
            ring
          · have hinsert : i ∈ insertOccupation i n := by
              simp [insertOccupation]
            have hrestore : removeOccupation i (insertOccupation i n) = n := by
              simp [removeOccupation, insertOccupation, hi]
            dsimp [f]
            rw [inner_completedBasisState_left, completedAnnihilate_apply, if_neg hi,
              toggleOccupation_of_not_mem hi,
              coe_completedFreeGibbsProbability_insertOccupation_of_not_mem ε β hi,
              completedAnnihilate_basisState_of_mem hinsert, map_smul, inner_smul_right,
              inner_completedBasisState_left, hrestore]
            have hexp :
                Complex.exp ((β : ℂ) * (ε i : ℂ)) *
                    Complex.exp (-(β : ℂ) * (ε i : ℂ)) = 1 := by
              rw [← Complex.exp_add]
              ring_nf
              exact Complex.exp_zero
            calc
              _ = 1 * ((purePointGibbsProbability (fermionEnergy ε) β n : ℂ) *
                  (fermionPhase i (insertOccupation i n) *
                    (A (completedBasisState n)) (insertOccupation i n))) := by ring
              _ = (Complex.exp ((β : ℂ) * (ε i : ℂ)) *
                    Complex.exp (-(β : ℂ) * (ε i : ℂ))) *
                    ((purePointGibbsProbability (fermionEnergy ε) β n : ℂ) *
                      (fermionPhase i (insertOccupation i n) *
                        (A (completedBasisState n)) (insertOccupation i n))) := by
                    rw [hexp]
              _ = _ := by ring
        _ = ∑' n : Occupation Mode, f n := by
          simpa [toggleOccupationEquiv_apply] using
            (Equiv.tsum_eq (toggleOccupationEquiv i) f)
        _ = ∑' n : Occupation Mode,
            Complex.exp ((β : ℂ) * (ε i : ℂ)) *
              ((purePointGibbsProbability (fermionEnergy ε) β n : ℂ) *
                inner ℂ (completedBasisState n)
                  ((A.comp (completedAnnihilate i)) (completedBasisState n))) := by
          rfl

/-- KMS rotation specialized to an ordered thermal-ladder tail. -/
theorem completedFreeGibbsExpectation_cons_eq_gibbsFactor_mul_rotate
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β)
    (C : CompletedThermalLadder Mode) (l : List (CompletedThermalLadder Mode)) :
    completedFreeGibbsExpectation ε β hsum (C :: l) =
      C.gibbsFactor ε β * completedFreeGibbsExpectation ε β hsum (l ++ [C]) := by
  rw [completedFreeGibbsExpectation, operatorProduct_cons,
    completedFreeGibbsExpectation_operator_comp ε β hsum C]
  rw [completedFreeGibbsExpectation, operatorProduct_append]
  simp

end CompletedThermalLadder

end
end Fermionic
end SecondQuantization
