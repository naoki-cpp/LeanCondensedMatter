import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.ModeTruncation
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.Hamiltonian
import LeanCondensedMatter.QuantumTheory.Gibbs.Boltzmann
import LeanCondensedMatter.Analysis.InfiniteSum.Truncation
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.Gibbs

set_option linter.style.header false

/-!
# Finite-mode truncation of the completed grand-canonical free-fermion Gibbs state

This module owns finite-mode truncations of the completed free-Gibbs state together with their
partition-function, probability, and bounded-expectation convergence to the full
`Common.grandCanonicalGibbsDensityOperator` at explicit chemical potential `μ`.
-/

namespace SecondQuantization
namespace Fermionic

open Filter Topology QuantumTheory

noncomputable section

variable {Mode : Type*}

/-- Classical decidable equality used consistently by finite-mode Gibbs truncations. -/
local instance completedGibbsModeTruncationDecidableEq : DecidableEq Mode := Classical.decEq Mode

/-- Free Boltzmann weight restricted to occupations using only modes from `S`. -/
noncomputable def completedFreeModeTruncatedWeight (ε : Mode → ℝ) (β μ : ℝ)
    (S : Finset Mode) (n : Occupation Mode) : ℝ :=
  if n ⊆ S then eigenbasisBoltzmannWeight (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β n else 0

private theorem completedFreeModeTruncatedWeight_nonneg (ε : Mode → ℝ) (β μ : ℝ)
    (S : Finset Mode) (n : Occupation Mode) :
    0 ≤ completedFreeModeTruncatedWeight ε β μ S n := by
  by_cases h : n ⊆ S
  · simp [completedFreeModeTruncatedWeight, h,
      eigenbasisBoltzmannWeight_nonneg]
  · simp [completedFreeModeTruncatedWeight, h]

private theorem completedFreeModeTruncatedWeight_norm_summable (ε : Mode → ℝ) (β μ : ℝ)
    (S : Finset Mode) :
    Summable fun n : Occupation Mode => ‖completedFreeModeTruncatedWeight ε β μ S n‖ := by
  apply summable_of_ne_finset_zero (s := S.powerset)
  intro n hn
  have hnot : ¬ n ⊆ S := by
    simpa using hn
  simp [completedFreeModeTruncatedWeight, hnot]

private theorem completedFreeModeTruncatedWeight_summable (ε : Mode → ℝ) (β μ : ℝ)
    (S : Finset Mode) :
    Summable (completedFreeModeTruncatedWeight ε β μ S) :=
  Summable.of_norm (completedFreeModeTruncatedWeight_norm_summable ε β μ S)

/-- Partition function of the Gibbs state restricted to the finite mode set `S`. -/
noncomputable def completedFreeModeTruncatedPartitionFunction (ε : Mode → ℝ) (β μ : ℝ)
    (S : Finset Mode) : ℝ :=
  ∑' n : Occupation Mode, completedFreeModeTruncatedWeight ε β μ S n

/-- Every finite-mode truncated partition function is strictly positive because the vacuum survives
all truncations. -/
theorem completedFreeModeTruncatedPartitionFunction_pos (ε : Mode → ℝ) (β μ : ℝ)
    (S : Finset Mode) :
    0 < completedFreeModeTruncatedPartitionFunction ε β μ S := by
  rw [completedFreeModeTruncatedPartitionFunction]
  exact (completedFreeModeTruncatedWeight_summable ε β μ S).tsum_pos
    (completedFreeModeTruncatedWeight_nonneg ε β μ S) vacuum
    (by
      have hvac : (vacuum : Occupation Mode) ⊆ S := by
        simpa [vacuum] using (Finset.empty_subset S)
      simpa [completedFreeModeTruncatedWeight, hvac] using
        eigenbasisBoltzmannWeight_pos (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β (vacuum : Occupation Mode))

/-- For each fixed occupation configuration, the finite-mode truncated Boltzmann weight is
eventually exactly the full pure-point Boltzmann weight. -/
theorem tendsto_completedFreeModeTruncatedWeight (ε : Mode → ℝ) (β μ : ℝ)
    (n : Occupation Mode) :
    Tendsto (fun S : Finset Mode => completedFreeModeTruncatedWeight ε β μ S n) atTop
      (𝓝 (eigenbasisBoltzmannWeight (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β n)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop n] with S hS
  have hsub : n ⊆ S := hS
  simp [completedFreeModeTruncatedWeight, hsub]

/-- Finite-mode partition functions converge to the full pure-point partition function. -/
theorem tendsto_completedFreeModeTruncatedPartitionFunction
    (ε : Mode → ℝ) (β μ : ℝ) (hsum : EigenbasisGibbsSummable
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β) :
    Tendsto (fun S : Finset Mode => completedFreeModeTruncatedPartitionFunction ε β μ S)
      atTop (𝓝 (eigenbasisPartitionFunction (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β)) := by
  simpa only [completedFreeModeTruncatedPartitionFunction,
    completedFreeModeTruncatedWeight, eigenbasisPartitionFunction] using
    (tendsto_tsum_ite_of_eventually
      (eigenbasisBoltzmannWeight
        (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β)
      hsum (atTop : Filter (Finset Mode))
      (fun S (n : Occupation Mode) => n ⊆ S)
      (fun n => eventually_ge_atTop n))

/-- Normalized Gibbs probability in the finite-mode truncated state. -/
noncomputable def completedFreeModeTruncatedGibbsProbability (ε : Mode → ℝ) (β μ : ℝ)
    (S : Finset Mode) (n : Occupation Mode) : ℝ :=
  (completedFreeModeTruncatedPartitionFunction ε β μ S)⁻¹ *
    completedFreeModeTruncatedWeight ε β μ S n

/-- Finite-mode truncated free Gibbs density operator, embedded in the full completed Fock space.
Its existence is unconditional: the truncated weight is supported on the finite powerset of `S`. -/
noncomputable def completedFreeModeTruncatedGibbsDensityOperator
    (ε : Mode → ℝ) (β μ : ℝ) (S : Finset Mode) :
    DensityOperator (CompletedFockSpace Mode) :=
  diagonalDensityOperator completedOccupationHilbertBasis
    (completedFreeModeTruncatedWeight ε β μ S)
    (completedFreeModeTruncatedWeight_norm_summable ε β μ S)
    (completedFreeModeTruncatedWeight_nonneg ε β μ S)
    (by simpa [completedFreeModeTruncatedPartitionFunction] using
      completedFreeModeTruncatedPartitionFunction_pos ε β μ S)

/-- The truncated density operator is diagonal with the normalized truncated Gibbs probability. -/
theorem completedFreeModeTruncatedGibbsDensityOperator_apply_basis
    (ε : Mode → ℝ) (β μ : ℝ) (S : Finset Mode) (n : Occupation Mode) :
    (completedFreeModeTruncatedGibbsDensityOperator ε β μ S).op (completedBasisState n) =
      (completedFreeModeTruncatedGibbsProbability ε β μ S n : ℂ) • completedBasisState n := by
  have hZ : 0 < ∑' m : Occupation Mode, completedFreeModeTruncatedWeight ε β μ S m := by
    simpa [completedFreeModeTruncatedPartitionFunction] using
      completedFreeModeTruncatedPartitionFunction_pos ε β μ S
  simpa [completedFreeModeTruncatedGibbsDensityOperator,
    completedFreeModeTruncatedGibbsProbability, completedFreeModeTruncatedPartitionFunction,
    Real.normalizedWeight] using
    diagonalDensityOperator_apply_basis completedOccupationHilbertBasis
      (completedFreeModeTruncatedWeight ε β μ S)
      (completedFreeModeTruncatedWeight_norm_summable ε β μ S)
      (completedFreeModeTruncatedWeight_nonneg ε β μ S) hZ n

/-- For every fixed occupation configuration, the normalized truncated Gibbs probability converges
to the full pure-point Gibbs probability. -/
theorem tendsto_completedFreeModeTruncatedGibbsProbability
    (ε : Mode → ℝ) (β μ : ℝ) (hsum : EigenbasisGibbsSummable
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β)
    (n : Occupation Mode) :
    Tendsto (fun S : Finset Mode => completedFreeModeTruncatedGibbsProbability ε β μ S n)
      atTop (𝓝 (eigenbasisGibbsProbability (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β n)) := by
  have hZne : eigenbasisPartitionFunction
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β ≠ 0 :=
    ne_of_gt (eigenbasisPartitionFunction_pos
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β hsum)
  change Tendsto (fun S : Finset Mode => Real.normalizedWeight
      (fun m : Occupation Mode => if m ⊆ S then
        eigenbasisBoltzmannWeight (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β m
        else 0) n) atTop
    (𝓝 (Real.normalizedWeight
      (eigenbasisBoltzmannWeight
        (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β) n))
  exact tendsto_normalizedWeight_ite_of_eventually
    (eigenbasisBoltzmannWeight
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β)
    hsum hZne (atTop : Filter (Finset Mode))
    (fun S (m : Occupation Mode) => m ⊆ S)
    (fun m => eventually_ge_atTop m) n

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

/-- Ratio converting a retained full-state Gibbs probability into the normalized truncated-state
probability. -/
noncomputable def completedFreeModeTruncationNormalizationRatio
    (ε : Mode → ℝ) (β μ : ℝ) (S : Finset Mode) : ℝ :=
  eigenbasisPartitionFunction (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β /
    completedFreeModeTruncatedPartitionFunction ε β μ S

/-- The finite-mode normalization correction tends to one. -/
theorem tendsto_completedFreeModeTruncationNormalizationRatio
    (ε : Mode → ℝ) (β μ : ℝ) (hsum : EigenbasisGibbsSummable
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β) :
    Tendsto (completedFreeModeTruncationNormalizationRatio ε β μ) atTop (𝓝 1) := by
  have hZ := tendsto_completedFreeModeTruncatedPartitionFunction ε β μ hsum
  have hZne : eigenbasisPartitionFunction (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β ≠ 0 :=
    ne_of_gt (eigenbasisPartitionFunction_pos (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β hsum)
  have hconst :
      Tendsto (fun _ : Finset Mode => eigenbasisPartitionFunction (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β) atTop
        (𝓝 (eigenbasisPartitionFunction (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β)) :=
    tendsto_const_nhds
  have hratio :
      Tendsto
        (fun S : Finset Mode =>
          eigenbasisPartitionFunction (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β /
            completedFreeModeTruncatedPartitionFunction ε β μ S)
        atTop
        (𝓝 (eigenbasisPartitionFunction (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β /
          eigenbasisPartitionFunction (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β)) :=
    hconst.div hZ hZne
  change Tendsto
    (fun S : Finset Mode =>
      eigenbasisPartitionFunction (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β /
        completedFreeModeTruncatedPartitionFunction ε β μ S)
    atTop (𝓝 1)
  simpa [div_self hZne] using hratio

/-- A truncated Gibbs probability is the retained full Gibbs probability multiplied by the finite
normalization correction. -/
theorem completedFreeModeTruncatedGibbsProbability_eq_ratio_mul
    (ε : Mode → ℝ) (β μ : ℝ) (hsum : EigenbasisGibbsSummable
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β)
    (S : Finset Mode) (n : Occupation Mode) :
    completedFreeModeTruncatedGibbsProbability ε β μ S n =
      completedFreeModeTruncationNormalizationRatio ε β μ S *
        (if n ⊆ S then eigenbasisGibbsProbability (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β n else 0) := by
  have hZne : eigenbasisPartitionFunction (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β ≠ 0 :=
    ne_of_gt (eigenbasisPartitionFunction_pos (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β hsum)
  have hZSne : completedFreeModeTruncatedPartitionFunction ε β μ S ≠ 0 :=
    ne_of_gt (completedFreeModeTruncatedPartitionFunction_pos ε β μ S)
  by_cases h : n ⊆ S
  · simp [completedFreeModeTruncatedGibbsProbability, completedFreeModeTruncatedWeight,
      completedFreeModeTruncationNormalizationRatio, eigenbasisGibbsProbability, h]
    field_simp [hZne, hZSne]
  · simp [completedFreeModeTruncatedGibbsProbability, completedFreeModeTruncatedWeight,
      completedFreeModeTruncationNormalizationRatio, h]

/-- The part of the full Gibbs expectation retained by a finite mode set, before finite-volume
renormalization. -/
noncomputable def completedFreeModeRetainedExpectation
    (ε : Mode → ℝ) (β μ : ℝ) (S : Finset Mode)
    (A : CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode) : ℂ :=
  ∑' n : Occupation Mode,
    if n ⊆ S then
      (eigenbasisGibbsProbability (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β n : ℂ) *
        inner ℂ (completedBasisState n) (A (completedBasisState n))
    else 0

/-- The retained, unrenormalized finite-mode expectation converges to the full Gibbs expectation for
every bounded operator. -/
theorem tendsto_completedFreeModeRetainedExpectation
    (ε : Mode → ℝ) (β μ : ℝ) (hsum : EigenbasisGibbsSummable
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β)
    (A : CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode) :
    Tendsto (fun S : Finset Mode => completedFreeModeRetainedExpectation ε β μ S A) atTop
      (𝓝 ((Common.grandCanonicalGibbsDensityOperator (Config := Occupation Mode) ε β μ hsum).expectation A)) := by
  let term : Occupation Mode → ℂ := fun n =>
    (eigenbasisGibbsProbability (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β n : ℂ) *
      inner ℂ (completedBasisState n) (A (completedBasisState n))
  have hsumDiag :
      HasSum term ((Common.grandCanonicalGibbsDensityOperator (Config := Occupation Mode) ε β μ hsum).expectation A) := by
    simpa only [term, completedOccupationHilbertBasis_apply] using
      (Common.grandCanonicalGibbsDensityOperator (Config := Occupation Mode) ε β μ hsum).hasSum_expectation_diagonal
        A completedOccupationHilbertBasis (eigenbasisGibbsProbability (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β)
        (fun n => by
          simpa using grandCanonicalGibbsDensityOperator_apply_basis ε β hsum n)
  have h := tendsto_tsum_ite_of_eventually term hsumDiag.summable.norm
    (atTop : Filter (Finset Mode))
    (fun S (n : Occupation Mode) => n ⊆ S)
    (fun n => eventually_ge_atTop n)
  rw [hsumDiag.tsum_eq] at h
  simpa [completedFreeModeRetainedExpectation, term] using h

/-- The expectation in a normalized finite-mode Gibbs state is its retained full-state expectation
times the normalization correction. -/
theorem completedFreeModeTruncatedGibbsDensityOperator_expectation_eq_ratio_mul
    (ε : Mode → ℝ) (β μ : ℝ) (hsum : EigenbasisGibbsSummable
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β)
    (S : Finset Mode)
    (A : CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode) :
    (completedFreeModeTruncatedGibbsDensityOperator ε β μ S).expectation A =
      (completedFreeModeTruncationNormalizationRatio ε β μ S : ℂ) *
        completedFreeModeRetainedExpectation ε β μ S A := by
  rw [(completedFreeModeTruncatedGibbsDensityOperator ε β μ S).expectation_eq_tsum_diagonal
    A completedOccupationHilbertBasis (completedFreeModeTruncatedGibbsProbability ε β μ S)
    (fun n => by
      simpa using completedFreeModeTruncatedGibbsDensityOperator_apply_basis ε β μ S n)]
  simp only [completedOccupationHilbertBasis_apply]
  unfold completedFreeModeRetainedExpectation
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  have hp := completedFreeModeTruncatedGibbsProbability_eq_ratio_mul ε β μ hsum S n
  have hpC :
      (completedFreeModeTruncatedGibbsProbability ε β μ S n : ℂ) =
        (completedFreeModeTruncationNormalizationRatio ε β μ S : ℂ) *
          (if n ⊆ S then (eigenbasisGibbsProbability (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β n : ℂ) else 0) := by
    rw [hp]
    by_cases h : n ⊆ S <;> simp [h]
  rw [hpC]
  by_cases h : n ⊆ S <;> simp [h, mul_assoc]

/-- Finite-mode completed Gibbs states converge weakly against every bounded operator. -/
theorem tendsto_completedFreeModeTruncatedGibbsDensityOperator_expectation
    (ε : Mode → ℝ) (β μ : ℝ) (hsum : EigenbasisGibbsSummable
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β)
    (A : CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode) :
    Tendsto
      (fun S : Finset Mode =>
        (completedFreeModeTruncatedGibbsDensityOperator ε β μ S).expectation A)
      atTop (𝓝 ((Common.grandCanonicalGibbsDensityOperator (Config := Occupation Mode) ε β μ hsum).expectation A)) := by
  have hratio :
      Tendsto (fun S : Finset Mode => (completedFreeModeTruncationNormalizationRatio ε β μ S : ℂ))
        atTop (𝓝 (1 : ℂ)) :=
    (tendsto_completedFreeModeTruncationNormalizationRatio ε β μ hsum).ofReal
  have hretained := tendsto_completedFreeModeRetainedExpectation ε β μ hsum A
  simpa using (hratio.mul hretained).congr'
    (Eventually.of_forall fun S =>
      (completedFreeModeTruncatedGibbsDensityOperator_expectation_eq_ratio_mul
        ε β μ hsum S A).symm)

end
end Fermionic
end SecondQuantization
