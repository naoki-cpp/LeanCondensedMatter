import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.GibbsModeTruncation
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.FreeGibbs
import Mathlib.Analysis.Normed.Group.Tannery

set_option linter.style.header false

/-!
# Weak convergence of finite-mode Gibbs truncations

This file completes the state-side C5 approximation layer.  The finite-mode Gibbs density operators
from `GibbsModeTruncation` converge to the generic pure-point free Gibbs state on completed Fock
space when tested against every bounded operator.  The topology is therefore explicit: this is weak
state convergence of bounded expectations, not a trace-norm convergence claim.
-/

namespace SecondQuantization
namespace Fermionic

open Filter Topology QuantumTheory

noncomputable section

variable {Mode : Type*}

/-- Classical decidable equality used consistently by finite-mode Gibbs expectation truncations. -/
local instance completedGibbsExpectationTruncationDecidableEq : DecidableEq Mode := Classical.decEq Mode

/-- Bounded-operator expectations in the truncated state are the corresponding occupation-basis
series. -/
theorem completedFreeModeTruncatedGibbsDensityOperator_expectation_eq_tsum
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β)
    (S : Finset Mode)
    (A : CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode) :
    (completedFreeModeTruncatedGibbsDensityOperator ε β hsum S).expectation A =
      ∑' n : Occupation Mode,
        (completedFreeModeTruncatedGibbsProbability ε β S n : ℂ) *
          inner ℂ (completedBasisState n) (A (completedBasisState n)) := by
  simpa using
    (completedFreeModeTruncatedGibbsDensityOperator ε β hsum S).expectation_eq_tsum_diagonal
      A completedOccupationHilbertBasis (completedFreeModeTruncatedGibbsProbability ε β S)
      (fun n => by
        simpa using completedFreeModeTruncatedGibbsDensityOperator_apply_basis ε β hsum S n)

/-- Ratio converting a retained full-state Gibbs probability into the normalized truncated-state
probability. -/
noncomputable def completedFreeModeTruncationNormalizationRatio
    (ε : Mode → ℝ) (β : ℝ) (S : Finset Mode) : ℝ :=
  purePointPartitionFunction (fermionEnergy ε) β /
    completedFreeModeTruncatedPartitionFunction ε β S

/-- The finite-mode normalization correction tends to one. -/
theorem tendsto_completedFreeModeTruncationNormalizationRatio
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β) :
    Tendsto (completedFreeModeTruncationNormalizationRatio ε β) atTop (𝓝 1) := by
  have hZ := tendsto_completedFreeModeTruncatedPartitionFunction ε β hsum
  have hZne : purePointPartitionFunction (fermionEnergy ε) β ≠ 0 :=
    ne_of_gt (purePointPartitionFunction_pos (fermionEnergy ε) β hsum)
  have hconst :
      Tendsto (fun _ : Finset Mode => purePointPartitionFunction (fermionEnergy ε) β) atTop
        (𝓝 (purePointPartitionFunction (fermionEnergy ε) β)) :=
    tendsto_const_nhds
  have hratio :
      Tendsto
        (fun S : Finset Mode =>
          purePointPartitionFunction (fermionEnergy ε) β /
            completedFreeModeTruncatedPartitionFunction ε β S)
        atTop
        (𝓝 (purePointPartitionFunction (fermionEnergy ε) β /
          purePointPartitionFunction (fermionEnergy ε) β)) :=
    hconst.div hZ hZne
  change Tendsto
    (fun S : Finset Mode =>
      purePointPartitionFunction (fermionEnergy ε) β /
        completedFreeModeTruncatedPartitionFunction ε β S)
    atTop (𝓝 1)
  simpa [div_self hZne] using hratio

/-- A truncated Gibbs probability is the retained full Gibbs probability multiplied by the finite
normalization correction. -/
theorem completedFreeModeTruncatedGibbsProbability_eq_ratio_mul
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β)
    (S : Finset Mode) (n : Occupation Mode) :
    completedFreeModeTruncatedGibbsProbability ε β S n =
      completedFreeModeTruncationNormalizationRatio ε β S *
        (if n ⊆ S then purePointGibbsProbability (fermionEnergy ε) β n else 0) := by
  have hZne : purePointPartitionFunction (fermionEnergy ε) β ≠ 0 :=
    ne_of_gt (purePointPartitionFunction_pos (fermionEnergy ε) β hsum)
  have hZSne : completedFreeModeTruncatedPartitionFunction ε β S ≠ 0 :=
    ne_of_gt (completedFreeModeTruncatedPartitionFunction_pos ε β hsum S)
  by_cases h : n ⊆ S
  · simp [completedFreeModeTruncatedGibbsProbability, completedFreeModeTruncatedWeight,
      completedFreeModeTruncationNormalizationRatio, purePointGibbsProbability, h]
    field_simp [hZne, hZSne]
  · simp [completedFreeModeTruncatedGibbsProbability, completedFreeModeTruncatedWeight,
      completedFreeModeTruncationNormalizationRatio, h]

/-- The part of the full Gibbs expectation retained by a finite mode set, before finite-volume
renormalization. -/
noncomputable def completedFreeModeRetainedExpectation
    (ε : Mode → ℝ) (β : ℝ) (S : Finset Mode)
    (A : CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode) : ℂ :=
  ∑' n : Occupation Mode,
    if n ⊆ S then
      (purePointGibbsProbability (fermionEnergy ε) β n : ℂ) *
        inner ℂ (completedBasisState n) (A (completedBasisState n))
    else 0

/-- The retained, unrenormalized finite-mode expectation converges to the full Gibbs expectation for
every bounded operator. -/
theorem tendsto_completedFreeModeRetainedExpectation
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β)
    (A : CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode) :
    Tendsto (fun S : Finset Mode => completedFreeModeRetainedExpectation ε β S A) atTop
      (𝓝 ((purePointGibbsDensityOperator completedOccupationHilbertBasis
        (fermionEnergy ε) β hsum).expectation A)) := by
  let term : Occupation Mode → ℂ := fun n =>
    (purePointGibbsProbability (fermionEnergy ε) β n : ℂ) *
      inner ℂ (completedBasisState n) (A (completedBasisState n))
  have hterm : Summable term := by
    simpa [term] using
      (purePointGibbsDensityOperator completedOccupationHilbertBasis
        (fermionEnergy ε) β hsum).summable_expectation_diagonal
        A completedOccupationHilbertBasis (purePointGibbsProbability (fermionEnergy ε) β)
        (fun n => by
          simpa using completedFreeGibbsDensityOperator_apply_basis ε β hsum n)
  have hpoint : ∀ n : Occupation Mode,
      Tendsto (fun S : Finset Mode => if n ⊆ S then term n else 0) atTop (𝓝 (term n)) := by
    intro n
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop n] with S hS
    have hsub : n ⊆ S := hS
    simp [hsub]
  have hbound :
      ∀ᶠ S : Finset Mode in atTop, ∀ n : Occupation Mode,
        ‖if n ⊆ S then term n else 0‖ ≤ ‖term n‖ := by
    filter_upwards [] with S
    intro n
    by_cases h : n ⊆ S <;> simp [h]
  have ht := tendsto_tsum_of_dominated_convergence hterm.norm hpoint hbound
  have hfull := completedFreeGibbsDensityOperator_expectation_eq_tsum ε β hsum A
  change (purePointGibbsDensityOperator completedOccupationHilbertBasis
    (fermionEnergy ε) β hsum).expectation A = ∑' n, term n at hfull
  rw [← hfull] at ht
  simpa [completedFreeModeRetainedExpectation, term] using ht

/-- The expectation in a normalized finite-mode Gibbs state is its retained full-state expectation
times the normalization correction. -/
theorem completedFreeModeTruncatedGibbsDensityOperator_expectation_eq_ratio_mul
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β)
    (S : Finset Mode)
    (A : CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode) :
    (completedFreeModeTruncatedGibbsDensityOperator ε β hsum S).expectation A =
      (completedFreeModeTruncationNormalizationRatio ε β S : ℂ) *
        completedFreeModeRetainedExpectation ε β S A := by
  rw [completedFreeModeTruncatedGibbsDensityOperator_expectation_eq_tsum]
  unfold completedFreeModeRetainedExpectation
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  have hp := completedFreeModeTruncatedGibbsProbability_eq_ratio_mul ε β hsum S n
  have hpC :
      (completedFreeModeTruncatedGibbsProbability ε β S n : ℂ) =
        (completedFreeModeTruncationNormalizationRatio ε β S : ℂ) *
          (if n ⊆ S then (purePointGibbsProbability (fermionEnergy ε) β n : ℂ) else 0) := by
    rw [hp]
    by_cases h : n ⊆ S <;> simp [h]
  rw [hpC]
  by_cases h : n ⊆ S <;> simp [h, mul_assoc]

/-- Finite-mode completed Gibbs states converge weakly against every bounded operator. -/
theorem tendsto_completedFreeModeTruncatedGibbsDensityOperator_expectation
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β)
    (A : CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode) :
    Tendsto
      (fun S : Finset Mode =>
        (completedFreeModeTruncatedGibbsDensityOperator ε β hsum S).expectation A)
      atTop (𝓝 ((purePointGibbsDensityOperator completedOccupationHilbertBasis
        (fermionEnergy ε) β hsum).expectation A)) := by
  have hratio :
      Tendsto (fun S : Finset Mode => (completedFreeModeTruncationNormalizationRatio ε β S : ℂ))
        atTop (𝓝 (1 : ℂ)) :=
    (tendsto_completedFreeModeTruncationNormalizationRatio ε β hsum).ofReal
  have hretained := tendsto_completedFreeModeRetainedExpectation ε β hsum A
  simpa using (hratio.mul hretained).congr'
    (Eventually.of_forall fun S =>
      (completedFreeModeTruncatedGibbsDensityOperator_expectation_eq_ratio_mul
        ε β hsum S A).symm)

end
end Fermionic
end SecondQuantization
