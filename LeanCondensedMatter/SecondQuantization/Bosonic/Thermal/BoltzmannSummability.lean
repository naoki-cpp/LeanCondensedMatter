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

variable {Mode : Type*} [Finite Mode]

/-- Positive one-particle energies make the free occupation Boltzmann weights absolutely summable. -/
theorem eigenbasisGibbsSummable_freeEigenvalue
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 < β) (hε : ∀ i, 0 < ε i) :
    EigenbasisGibbsSummable (freeEigenvalue ε) β := by
  letI := Fintype.ofFinite Mode
  unfold EigenbasisGibbsSummable
  have hsum := summable_boltzmannWeight ε β (fun i => mul_pos hβ (hε i))
  exact hsum.congr fun n => by
    simp [boltzmannWeight, eigenbasisBoltzmannWeight, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_nonneg _)]

/-- The convergence-aware algebraic bosonic partition function is the canonical pure-point
partition function for the free occupation energies. -/
theorem freeGibbsPartition_eq_coe_eigenbasisPartitionFunction
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 < β) (hε : ∀ i, 0 < ε i) :
    freeGibbsPartition ε β =
      (eigenbasisPartitionFunction (freeEigenvalue ε) β : ℂ) := by
  letI := Fintype.ofFinite Mode
  rw [freeGibbsPartition_eq_tsum ε β (fun i => mul_pos hβ (hε i))]
  congr 1

end
end Bosonic
end SecondQuantization
