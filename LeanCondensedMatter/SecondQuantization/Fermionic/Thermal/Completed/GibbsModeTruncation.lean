import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.ModeTruncation
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeBoltzmannCore
import LeanCondensedMatter.QuantumTheory.Gibbs.PurePoint
import Mathlib.Analysis.Normed.Group.Tannery

set_option linter.style.header false

/-!
# Finite-mode truncations of the completed free Gibbs state

For a finite mode set `S`, the truncated Gibbs weight keeps exactly occupation configurations
contained in `S` and vanishes on all others.  The resulting normalized diagonal density operator
lives on the full completed Fock space, but is supported on the finite-mode sector selected by `S`.

As `S` tends to `atTop` in `Finset Mode`, the unnormalized truncated weights converge pointwise to
the generic pure-point free-fermion weights.  Absolute Gibbs summability gives a single summable
dominating family, so Tannery's theorem yields convergence of the truncated partition functions.
Consequently the normalized occupation probabilities converge pointwise to the generic pure-point
Gibbs probabilities.
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
