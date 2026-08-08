import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.ModeTruncation
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.FreeGibbs
import Mathlib.Analysis.Normed.Group.Tannery

set_option linter.style.header false

/-!
# Finite-mode truncations of the completed free Gibbs state

For a finite mode set `S`, the truncated Gibbs weight keeps exactly occupation configurations
contained in `S` and vanishes on all others.  The resulting normalized diagonal density operator
lives on the full completed Fock space, but is supported on the finite-mode sector selected by `S`.

As `S` tends to `atTop` in `Finset Mode`, the unnormalized truncated weights converge pointwise to
the full Boltzmann weights.  Absolute Gibbs summability gives a single summable dominating family,
so Tannery's theorem yields convergence of the truncated partition functions.  Consequently the
normalized occupation probabilities converge pointwise to the full Gibbs probabilities.
-/

namespace SecondQuantization
namespace Fermionic

open Filter Topology QuantumTheory

noncomputable section

variable {Mode : Type*}

/-- Free Boltzmann weight restricted to occupations using only modes from `S`. -/
noncomputable def completedFreeModeTruncatedWeight (ε : Mode → ℝ) (β : ℝ)
    (S : Finset Mode) (n : Occupation Mode) : ℝ := by
  classical
  exact if n ⊆ S then completedFreeBoltzmannRealWeight ε β n else 0

@[simp]
theorem completedFreeModeTruncatedWeight_apply (ε : Mode → ℝ) (β : ℝ)
    (S : Finset Mode) (n : Occupation Mode) :
    completedFreeModeTruncatedWeight ε β S n =
      if n ⊆ S then completedFreeBoltzmannRealWeight ε β n else 0 := by
  classical
  simp [completedFreeModeTruncatedWeight]

/-- Truncated Boltzmann weights remain nonnegative. -/
theorem completedFreeModeTruncatedWeight_nonneg (ε : Mode → ℝ) (β : ℝ)
    (S : Finset Mode) (n : Occupation Mode) :
    0 ≤ completedFreeModeTruncatedWeight ε β S n := by
  classical
  by_cases h : n ⊆ S
  · simp [completedFreeModeTruncatedWeight, h,
      completedFreeBoltzmannRealWeight_nonneg]
  · simp [completedFreeModeTruncatedWeight, h]

/-- Absolute summability of the full Gibbs weights dominates every finite-mode truncation. -/
theorem completedFreeModeTruncatedWeight_norm_summable (ε : Mode → ℝ) (β : ℝ)
    (hsum : CompletedFreeGibbsSummable ε β) (S : Finset Mode) :
    Summable fun n : Occupation Mode => ‖completedFreeModeTruncatedWeight ε β S n‖ := by
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
  · intro n
    classical
    by_cases h : n ⊆ S
    · simp [completedFreeModeTruncatedWeight, h]
    · simp [completedFreeModeTruncatedWeight, h]
  · exact hsum

/-- Ordinary summability of each truncated Boltzmann family. -/
theorem completedFreeModeTruncatedWeight_summable (ε : Mode → ℝ) (β : ℝ)
    (hsum : CompletedFreeGibbsSummable ε β) (S : Finset Mode) :
    Summable (completedFreeModeTruncatedWeight ε β S) :=
  Summable.of_norm (completedFreeModeTruncatedWeight_norm_summable ε β hsum S)

/-- Partition function of the Gibbs state restricted to the finite mode set `S`. -/
noncomputable def completedFreeModeTruncatedPartitionFunction (ε : Mode → ℝ) (β : ℝ)
    (S : Finset Mode) : ℝ :=
  ∑' n : Occupation Mode, completedFreeModeTruncatedWeight ε β S n

/-- Every finite-mode truncated partition function is strictly positive because the vacuum survives
all truncations. -/
theorem completedFreeModeTruncatedPartitionFunction_pos (ε : Mode → ℝ) (β : ℝ)
    (hsum : CompletedFreeGibbsSummable ε β) (S : Finset Mode) :
    0 < completedFreeModeTruncatedPartitionFunction ε β S := by
  rw [completedFreeModeTruncatedPartitionFunction]
  exact (completedFreeModeTruncatedWeight_summable ε β hsum S).tsum_pos
    (completedFreeModeTruncatedWeight_nonneg ε β S) vacuum
    (by
      classical
      simp [completedFreeModeTruncatedWeight,
        completedFreeBoltzmannRealWeight_pos])

/-- For each fixed occupation configuration, the finite-mode truncated Boltzmann weight is
eventually exactly the full Boltzmann weight. -/
theorem tendsto_completedFreeModeTruncatedWeight (ε : Mode → ℝ) (β : ℝ)
    (n : Occupation Mode) :
    Tendsto (fun S : Finset Mode => completedFreeModeTruncatedWeight ε β S n) atTop
      (𝓝 (completedFreeBoltzmannRealWeight ε β n)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop n] with S hS
  simp [completedFreeModeTruncatedWeight, hS]

/-- Finite-mode partition functions converge to the full completed partition function. -/
theorem tendsto_completedFreeModeTruncatedPartitionFunction
    (ε : Mode → ℝ) (β : ℝ) (hsum : CompletedFreeGibbsSummable ε β) :
    Tendsto (fun S : Finset Mode => completedFreeModeTruncatedPartitionFunction ε β S)
      atTop (𝓝 (completedFreePartitionFunction ε β)) := by
  have hbound :
      ∀ᶠ S : Finset Mode in atTop, ∀ n : Occupation Mode,
        ‖completedFreeModeTruncatedWeight ε β S n‖ ≤
          ‖completedFreeBoltzmannRealWeight ε β n‖ := by
    filter_upwards [] with S
    intro n
    classical
    by_cases h : n ⊆ S
    · simp [completedFreeModeTruncatedWeight, h]
    · simp [completedFreeModeTruncatedWeight, h]
  have h := tendsto_tsum_of_dominated_convergence hsum
    (fun n => tendsto_completedFreeModeTruncatedWeight ε β n) hbound
  simpa [completedFreeModeTruncatedPartitionFunction, completedFreePartitionFunction] using h

/-- Normalized Gibbs probability in the finite-mode truncated state. -/
noncomputable def completedFreeModeTruncatedGibbsProbability (ε : Mode → ℝ) (β : ℝ)
    (S : Finset Mode) (n : Occupation Mode) : ℝ :=
  (completedFreeModeTruncatedPartitionFunction ε β S)⁻¹ *
    completedFreeModeTruncatedWeight ε β S n

/-- Truncated normalized probabilities are nonnegative. -/
theorem completedFreeModeTruncatedGibbsProbability_nonneg (ε : Mode → ℝ) (β : ℝ)
    (hsum : CompletedFreeGibbsSummable ε β) (S : Finset Mode) (n : Occupation Mode) :
    0 ≤ completedFreeModeTruncatedGibbsProbability ε β S n := by
  exact mul_nonneg
    (inv_nonneg.mpr (completedFreeModeTruncatedPartitionFunction_pos ε β hsum S).le)
    (completedFreeModeTruncatedWeight_nonneg ε β S n)

/-- Finite-mode truncated free Gibbs density operator, embedded in the full completed Fock space. -/
noncomputable def completedFreeModeTruncatedGibbsDensityOperator
    (ε : Mode → ℝ) (β : ℝ) (hsum : CompletedFreeGibbsSummable ε β) (S : Finset Mode) :
    DensityOperator (CompletedFockSpace Mode) :=
  diagonalDensityOperator completedOccupationHilbertBasis
    (completedFreeModeTruncatedWeight ε β S)
    (completedFreeModeTruncatedWeight_norm_summable ε β hsum S)
    (completedFreeModeTruncatedWeight_nonneg ε β S)
    (by simpa [completedFreeModeTruncatedPartitionFunction] using
      completedFreeModeTruncatedPartitionFunction_pos ε β hsum S)

/-- The truncated density operator is diagonal with the normalized truncated Gibbs probability. -/
theorem completedFreeModeTruncatedGibbsDensityOperator_apply_basis
    (ε : Mode → ℝ) (β : ℝ) (hsum : CompletedFreeGibbsSummable ε β)
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
to the full completed Gibbs probability. -/
theorem tendsto_completedFreeModeTruncatedGibbsProbability
    (ε : Mode → ℝ) (β : ℝ) (hsum : CompletedFreeGibbsSummable ε β)
    (n : Occupation Mode) :
    Tendsto (fun S : Finset Mode => completedFreeModeTruncatedGibbsProbability ε β S n)
      atTop (𝓝 (completedFreeGibbsProbability ε β n)) := by
  have hZ := tendsto_completedFreeModeTruncatedPartitionFunction ε β hsum
  have hZne : completedFreePartitionFunction ε β ≠ 0 :=
    ne_of_gt (completedFreePartitionFunction_pos ε β hsum)
  have hw := tendsto_completedFreeModeTruncatedWeight ε β n
  simpa [completedFreeModeTruncatedGibbsProbability, completedFreeGibbsProbability] using
    (hZ.inv₀ hZne).mul hw

end
end Fermionic
end SecondQuantization
