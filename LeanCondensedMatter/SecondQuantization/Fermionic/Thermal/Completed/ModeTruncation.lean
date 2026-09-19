import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.ModeTruncation
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeBoltzmannCore
import LeanCondensedMatter.QuantumTheory.Gibbs.PurePoint
import Mathlib.Analysis.Normed.Group.Tannery
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.Gibbs

set_option linter.style.header false

/-!
# Finite-mode truncation of the completed free-fermion Gibbs state

This module owns finite-mode truncations of the completed free-Gibbs state together with their
partition-function, probability, and bounded-expectation convergence to the full pure-point Gibbs
state.
-/

namespace SecondQuantization
namespace Fermionic

open Filter Topology QuantumTheory

noncomputable section

variable {Mode : Type*}

/-- Classical decidable equality used consistently by finite-mode Gibbs truncations. -/
local instance completedGibbsModeTruncationDecidableEq : DecidableEq Mode := Classical.decEq Mode

/-- Free Boltzmann weight restricted to occupations using only modes from `S`. -/
noncomputable def completedFreeModeTruncatedWeight (ε : Mode → ℝ) (β : ℝ)
    (S : Finset Mode) (n : Occupation Mode) : ℝ :=
  if n ⊆ S then purePointBoltzmannWeight (fermionEnergy ε) β n else 0

private theorem completedFreeModeTruncatedWeight_nonneg (ε : Mode → ℝ) (β : ℝ)
    (S : Finset Mode) (n : Occupation Mode) :
    0 ≤ completedFreeModeTruncatedWeight ε β S n := by
  by_cases h : n ⊆ S
  · simp [completedFreeModeTruncatedWeight, h,
      purePointBoltzmannWeight_nonneg]
  · simp [completedFreeModeTruncatedWeight, h]

private theorem completedFreeModeTruncatedWeight_norm_summable (ε : Mode → ℝ) (β : ℝ)
    (hsum : PurePointGibbsSummable (fermionEnergy ε) β) (S : Finset Mode) :
    Summable fun n : Occupation Mode => ‖completedFreeModeTruncatedWeight ε β S n‖ := by
  exact Summable.of_nonneg_of_le
    (f := fun n : Occupation Mode => ‖purePointBoltzmannWeight (fermionEnergy ε) β n‖)
    (g := fun n : Occupation Mode => ‖completedFreeModeTruncatedWeight ε β S n‖)
    (fun n => norm_nonneg _)
    (fun n => by
      by_cases h : n ⊆ S
      · simp [completedFreeModeTruncatedWeight, h]
      · simp [completedFreeModeTruncatedWeight, h])
    hsum

private theorem completedFreeModeTruncatedWeight_summable (ε : Mode → ℝ) (β : ℝ)
    (hsum : PurePointGibbsSummable (fermionEnergy ε) β) (S : Finset Mode) :
    Summable (completedFreeModeTruncatedWeight ε β S) :=
  Summable.of_norm (completedFreeModeTruncatedWeight_norm_summable ε β hsum S)

/-- Partition function of the Gibbs state restricted to the finite mode set `S`. -/
noncomputable def completedFreeModeTruncatedPartitionFunction (ε : Mode → ℝ) (β : ℝ)
    (S : Finset Mode) : ℝ :=
  ∑' n : Occupation Mode, completedFreeModeTruncatedWeight ε β S n

/-- Every finite-mode truncated partition function is strictly positive because the vacuum survives
all truncations. -/
theorem completedFreeModeTruncatedPartitionFunction_pos (ε : Mode → ℝ) (β : ℝ)
    (hsum : PurePointGibbsSummable (fermionEnergy ε) β) (S : Finset Mode) :
    0 < completedFreeModeTruncatedPartitionFunction ε β S := by
  rw [completedFreeModeTruncatedPartitionFunction]
  exact (completedFreeModeTruncatedWeight_summable ε β hsum S).tsum_pos
    (completedFreeModeTruncatedWeight_nonneg ε β S) vacuum
    (by
      have hvac : (vacuum : Occupation Mode) ⊆ S := by
        simpa [vacuum] using (Finset.empty_subset S)
      simpa [completedFreeModeTruncatedWeight, hvac] using
        purePointBoltzmannWeight_pos (fermionEnergy ε) β (vacuum : Occupation Mode))

/-- For each fixed occupation configuration, the finite-mode truncated Boltzmann weight is
eventually exactly the full pure-point Boltzmann weight. -/
theorem tendsto_completedFreeModeTruncatedWeight (ε : Mode → ℝ) (β : ℝ)
    (n : Occupation Mode) :
    Tendsto (fun S : Finset Mode => completedFreeModeTruncatedWeight ε β S n) atTop
      (𝓝 (purePointBoltzmannWeight (fermionEnergy ε) β n)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop n] with S hS
  have hsub : n ⊆ S := hS
  simp [completedFreeModeTruncatedWeight, hsub]

/-- Finite-mode partition functions converge to the full pure-point partition function. -/
theorem tendsto_completedFreeModeTruncatedPartitionFunction
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β) :
    Tendsto (fun S : Finset Mode => completedFreeModeTruncatedPartitionFunction ε β S)
      atTop (𝓝 (purePointPartitionFunction (fermionEnergy ε) β)) := by
  have hbound :
      ∀ᶠ S : Finset Mode in atTop, ∀ n : Occupation Mode,
        ‖completedFreeModeTruncatedWeight ε β S n‖ ≤
          ‖purePointBoltzmannWeight (fermionEnergy ε) β n‖ := by
    filter_upwards [] with S
    intro n
    by_cases h : n ⊆ S
    · simp [completedFreeModeTruncatedWeight, h]
    · simp [completedFreeModeTruncatedWeight, h]
  have h := tendsto_tsum_of_dominated_convergence hsum
    (fun n => tendsto_completedFreeModeTruncatedWeight ε β n) hbound
  simpa [completedFreeModeTruncatedPartitionFunction, purePointPartitionFunction] using h

/-- Normalized Gibbs probability in the finite-mode truncated state. -/
noncomputable def completedFreeModeTruncatedGibbsProbability (ε : Mode → ℝ) (β : ℝ)
    (S : Finset Mode) (n : Occupation Mode) : ℝ :=
  (completedFreeModeTruncatedPartitionFunction ε β S)⁻¹ *
    completedFreeModeTruncatedWeight ε β S n

/-- Finite-mode truncated free Gibbs density operator, embedded in the full completed Fock space. -/
noncomputable def completedFreeModeTruncatedGibbsDensityOperator
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β)
    (S : Finset Mode) :
    DensityOperator (CompletedFockSpace Mode) :=
  diagonalDensityOperator completedOccupationHilbertBasis
    (completedFreeModeTruncatedWeight ε β S)
    (completedFreeModeTruncatedWeight_norm_summable ε β hsum S)
    (completedFreeModeTruncatedWeight_nonneg ε β S)
    (by simpa [completedFreeModeTruncatedPartitionFunction] using
      completedFreeModeTruncatedPartitionFunction_pos ε β hsum S)

/-- The truncated density operator is diagonal with the normalized truncated Gibbs probability. -/
theorem completedFreeModeTruncatedGibbsDensityOperator_apply_basis
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β)
    (S : Finset Mode) (n : Occupation Mode) :
    (completedFreeModeTruncatedGibbsDensityOperator ε β hsum S).op (completedBasisState n) =
      (completedFreeModeTruncatedGibbsProbability ε β S n : ℂ) • completedBasisState n := by
  have hZ : 0 < ∑' m : Occupation Mode, completedFreeModeTruncatedWeight ε β S m := by
    simpa [completedFreeModeTruncatedPartitionFunction] using
      completedFreeModeTruncatedPartitionFunction_pos ε β hsum S
  simpa [completedFreeModeTruncatedGibbsDensityOperator,
    completedFreeModeTruncatedGibbsProbability, completedFreeModeTruncatedPartitionFunction,
    normalizedDiagonalWeight] using
    diagonalDensityOperator_apply_basis completedOccupationHilbertBasis
      (completedFreeModeTruncatedWeight ε β S)
      (completedFreeModeTruncatedWeight_norm_summable ε β hsum S)
      (completedFreeModeTruncatedWeight_nonneg ε β S) hZ n

/-- For every fixed occupation configuration, the normalized truncated Gibbs probability converges
to the full pure-point Gibbs probability. -/
theorem tendsto_completedFreeModeTruncatedGibbsProbability
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β)
    (n : Occupation Mode) :
    Tendsto (fun S : Finset Mode => completedFreeModeTruncatedGibbsProbability ε β S n)
      atTop (𝓝 (purePointGibbsProbability (fermionEnergy ε) β n)) := by
  have hZ := tendsto_completedFreeModeTruncatedPartitionFunction ε β hsum
  have hZne : purePointPartitionFunction (fermionEnergy ε) β ≠ 0 :=
    ne_of_gt (purePointPartitionFunction_pos (fermionEnergy ε) β hsum)
  have hw := tendsto_completedFreeModeTruncatedWeight ε β n
  simpa [completedFreeModeTruncatedGibbsProbability, purePointGibbsProbability] using
    (hZ.inv₀ hZne).mul hw

end
end Fermionic
end SecondQuantization

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
