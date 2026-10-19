import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.ConvergenceAwareGibbs
import LeanCondensedMatter.QuantumTheory.Gibbs.Boltzmann

set_option linter.style.header false

/-!
# Boltzmann summability for the free boson Gibbs state

For finitely many bosonic modes with strictly positive one-particle energies at positive inverse
temperature, the existing occupation-level Boltzmann summability theorem supplies the generic
`QuantumTheory.EigenbasisGibbsSummable` hypothesis for `freeEigenvalue ε`.

This module is representation-independent: it also identifies the convergence-aware algebraic
`freeGibbsPartition` with the canonical pure-point partition function. Completed-space heat and
density operators consume these results downstream.
-/

namespace SecondQuantization
namespace Bosonic

open QuantumTheory

noncomputable section

variable {Mode : Type*}

/-- For arbitrary mode types, the canonical pure-point Gibbs summability condition is exactly
summability of the free-boson occupation Boltzmann weights. No mode finiteness is needed. -/
theorem eigenbasisGibbsSummable_freeEigenvalue_iff_boltzmannWeight_summable
    (ε : Mode → ℝ) (β : ℝ) :
    EigenbasisGibbsSummable (freeEigenvalue ε) β ↔
      Summable (boltzmannWeight ε β) := by
  unfold EigenbasisGibbsSummable
  simp only [eigenbasisBoltzmannWeight, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_nonneg _)]
  rfl

/-- The algebraic occupation trace and the canonical pure-point partition sum are the same
for arbitrary bosonic mode types. This coordinate identity does not assert convergence. -/
theorem freeGibbsPartition_eq_coe_eigenbasisPartitionFunction
    (ε : Mode → ℝ) (β : ℝ) :
    freeGibbsPartition ε β =
      (eigenbasisPartitionFunction (freeEigenvalue ε) β : ℂ) := by
  unfold freeGibbsPartition Common.tsumTrace eigenbasisPartitionFunction
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  simp only [matrixCoeff_imaginaryTimeEvolveFree_self, eigenbasisBoltzmannWeight,
    Complex.ofReal_exp]

variable [Finite Mode]

/-- Positive one-particle energies make the free occupation Boltzmann weights absolutely summable. -/
theorem eigenbasisGibbsSummable_freeEigenvalue
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 < β) (hε : ∀ i, 0 < ε i) :
    EigenbasisGibbsSummable (freeEigenvalue ε) β := by
  apply (eigenbasisGibbsSummable_freeEigenvalue_iff_boltzmannWeight_summable ε β).2
  letI := Fintype.ofFinite Mode
  exact summable_boltzmannWeight ε β (fun i => mul_pos hβ (hε i))


end
end Bosonic
end SecondQuantization
