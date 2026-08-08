import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.ThermalPeel

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

omit [LinearOrder Mode] in
/-- A completed occupation basis vector extracts the corresponding coordinate by inner product. -/
@[simp]
theorem inner_completedBasisState (n : Occupation Mode) (ψ : CompletedFockSpace Mode) :
    inner ℂ (completedBasisState n) ψ = ψ n := by
  classical
  simpa [completedBasisState] using (lp.inner_single_left (𝕜 := ℂ) n (1 : ℂ) ψ)

/-- Toggling the acted-on mode does not change its fermionic Jordan--Wigner phase. -/
@[simp]
theorem fermionPhase_toggleOccupation (i : Mode) (n : Occupation Mode) :
    fermionPhase i (toggleOccupation i n) = fermionPhase i n := by
  by_cases hi : i ∈ n
  · rw [toggleOccupation_of_mem hi]
    have hf :
        (removeOccupation i n).filter (· < i) = n.filter (· < i) := by
      ext x
      simp only [removeOccupation, Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨_, hxn⟩, hlt⟩
        exact ⟨hxn, hlt⟩
      · rintro ⟨hxn, hlt⟩
        exact ⟨⟨ne_of_lt hlt, hxn⟩, hlt⟩
    simp only [fermionPhase, fermionSign, hf]
  · rw [toggleOccupation_of_not_mem hi]
    have hf :
        (insertOccupation i n).filter (· < i) = n.filter (· < i) := by
      ext x
      simp only [insertOccupation, Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hx, hlt⟩
        rcases hx with rfl | hxn
        · exact (lt_irrefl i hlt).elim
        · exact ⟨hxn, hlt⟩
      · rintro ⟨hxn, hlt⟩
        exact ⟨Or.inr hxn, hlt⟩
    simp only [fermionPhase, fermionSign, hf]

/-- Completed free-Gibbs KMS rotation for one thermal ladder and an arbitrary bounded operator:
`⟨C A⟩β = gβ(C) ⟨A C⟩β`.  The scalar `gβ(C)` is the same factor appearing in
`ρβ C = gβ(C) C ρβ`. -/
theorem completedFreeGibbsExpectation_operator_comp
    (ε : Mode → ℝ) (β : ℝ) (hsum : CompletedFreeGibbsSummable ε β)
    (C : CompletedThermalLadder Mode)
    (A : CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode) :
    (completedFreeGibbsDensityOperator ε β hsum).expectation (C.operator.comp A) =
      C.gibbsFactor ε β *
        (completedFreeGibbsDensityOperator ε β hsum).expectation (A.comp C.operator) := by
  rw [completedFreeGibbsDensityOperator_expectation_eq_tsum,
    completedFreeGibbsDensityOperator_expectation_eq_tsum, ← tsum_mul_left]
  cases C with
  | create i =>
      simp only [operator_create, gibbsFactor_create]
      let f : Occupation Mode → ℂ := fun n =>
        Complex.exp (-(β : ℂ) * (ε i : ℂ)) *
          ((completedFreeGibbsProbability ε β n : ℂ) *
            inner ℂ (completedBasisState n)
              ((A.comp (completedCreate i)) (completedBasisState n)))
      calc
        (∑' n : Occupation Mode,
            (completedFreeGibbsProbability ε β n : ℂ) *
              inner ℂ (completedBasisState n)
                (((completedCreate i).comp A) (completedBasisState n))) =
            ∑' n : Occupation Mode, f (toggleOccupation i n) := by
          apply tsum_congr
          intro n
          by_cases hi : i ∈ n
          · have hit : i ∉ toggleOccupation i n := by simp [hi]
            have htoggle : toggleOccupation i (toggleOccupation i n) = n :=
              toggleOccupation_involutive i n
            dsimp [f]
            rw [ContinuousLinearMap.comp_apply, inner_completedBasisState,
              completedCreate_apply, if_pos hi, toggleOccupation_of_mem hi,
              coe_completedFreeGibbsProbability_removeOccupation_of_mem ε β hi,
              ContinuousLinearMap.comp_apply,
              completedCreate_basisState_of_not_mem hit, map_smul, inner_smul_right,
              inner_completedBasisState, htoggle]
            rw [← Complex.exp_add]
            ring_nf
            simp
          · have hit : i ∈ toggleOccupation i n := by simp [hi]
            dsimp [f]
            rw [ContinuousLinearMap.comp_apply, inner_completedBasisState,
              completedCreate_apply, if_neg hi, ContinuousLinearMap.comp_apply,
              completedCreate_basisState_of_mem hit]
            simp
        _ = ∑' n : Occupation Mode, f n := by
          simpa [toggleOccupationEquiv_apply] using
            (Equiv.tsum_eq (toggleOccupationEquiv i) f)
        _ = ∑' n : Occupation Mode,
            Complex.exp (-(β : ℂ) * (ε i : ℂ)) *
              ((completedFreeGibbsProbability ε β n : ℂ) *
                inner ℂ (completedBasisState n)
                  ((A.comp (completedCreate i)) (completedBasisState n))) := by
          rfl
  | annihilate i =>
      simp only [operator_annihilate, gibbsFactor_annihilate]
      let f : Occupation Mode → ℂ := fun n =>
        Complex.exp ((β : ℂ) * (ε i : ℂ)) *
          ((completedFreeGibbsProbability ε β n : ℂ) *
            inner ℂ (completedBasisState n)
              ((A.comp (completedAnnihilate i)) (completedBasisState n)))
      calc
        (∑' n : Occupation Mode,
            (completedFreeGibbsProbability ε β n : ℂ) *
              inner ℂ (completedBasisState n)
                (((completedAnnihilate i).comp A) (completedBasisState n))) =
            ∑' n : Occupation Mode, f (toggleOccupation i n) := by
          apply tsum_congr
          intro n
          by_cases hi : i ∈ n
          · have hit : i ∉ toggleOccupation i n := by simp [hi]
            dsimp [f]
            rw [ContinuousLinearMap.comp_apply, inner_completedBasisState,
              completedAnnihilate_apply, if_pos hi, ContinuousLinearMap.comp_apply,
              completedAnnihilate_basisState_of_not_mem hit]
            simp
          · have hit : i ∈ toggleOccupation i n := by simp [hi]
            have htoggle : toggleOccupation i (toggleOccupation i n) = n :=
              toggleOccupation_involutive i n
            dsimp [f]
            rw [ContinuousLinearMap.comp_apply, inner_completedBasisState,
              completedAnnihilate_apply, if_neg hi, toggleOccupation_of_not_mem hi,
              coe_completedFreeGibbsProbability_insertOccupation_of_not_mem ε β hi,
              ContinuousLinearMap.comp_apply,
              completedAnnihilate_basisState_of_mem hit, map_smul, inner_smul_right,
              inner_completedBasisState, htoggle]
            rw [← Complex.exp_add]
            ring_nf
            simp
        _ = ∑' n : Occupation Mode, f n := by
          simpa [toggleOccupationEquiv_apply] using
            (Equiv.tsum_eq (toggleOccupationEquiv i) f)
        _ = ∑' n : Occupation Mode,
            Complex.exp ((β : ℂ) * (ε i : ℂ)) *
              ((completedFreeGibbsProbability ε β n : ℂ) *
                inner ℂ (completedBasisState n)
                  ((A.comp (completedAnnihilate i)) (completedBasisState n))) := by
          rfl

/-- KMS rotation specialized to an ordered thermal-ladder tail. -/
theorem completedFreeGibbsExpectation_cons_eq_gibbsFactor_mul_rotate
    (ε : Mode → ℝ) (β : ℝ) (hsum : CompletedFreeGibbsSummable ε β)
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
