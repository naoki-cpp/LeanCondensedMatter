import LeanCondensedMatter.QuantumTheory.Gibbs.FreeExchangeCycleSeries

set_option linter.style.header false

/-!
# Free-boson connected-cycle and grand-partition series

The free-boson formal grand product is the `ζ = +1` specialization of the shared Gibbs-level
Bose/Fermi backend. This module keeps the bosonic domain-facing names while delegating the formal
product, logarithm, and connected-cycle proof to that shared owner.

The actual convergent bosonic occupation-space partition sum is handled separately by the bosonic
analytic thermal layer. No formal power series is evaluated at `t = 1` here.
-/

namespace SecondQuantization
namespace Bosonic

variable {Mode : Type*}

/-- Formal finite-mode free-boson grand-partition series
`𝒵_B(t) = ∏ᵢ (1 - exp(-β εᵢ) t)⁻¹`. -/
noncomputable def freeGrandPartitionSeries [Fintype Mode]
    (ε : Mode → ℝ) (β : ℝ) : PowerSeries ℂ :=
  QuantumTheory.freeExchangeGrandPartitionSeries (1 : ℂ) (Or.inl rfl) ε β

@[simp]
theorem constantCoeff_freeGrandPartitionSeries [Fintype Mode]
    (ε : Mode → ℝ) (β : ℝ) :
    PowerSeries.constantCoeff (freeGrandPartitionSeries ε β) = 1 := by
  unfold freeGrandPartitionSeries
  exact
    QuantumTheory.constantCoeff_freeExchangeGrandPartitionSeries
      (1 : ℂ) (Or.inl rfl) ε β

/-- Free-boson formal linked-cluster identity: the logarithm of the finite grand product equals the
`ζ = +1` connected-cycle series. -/
theorem logOf_freeGrandPartitionSeries_eq_permutationConnectedCycleSeries
    [Fintype Mode] (ε : Mode → ℝ) (β : ℝ) :
    PowerSeries.logOf (freeGrandPartitionSeries ε β) =
      Combinatorics.permutationConnectedCycleSeries 1
        (QuantumTheory.freeBoltzmannModeKernel ε β) := by
  unfold freeGrandPartitionSeries
  exact
    QuantumTheory.logOf_freeExchangeGrandPartitionSeries_eq_permutationConnectedCycleSeries
      (1 : ℂ) (Or.inl rfl) ε β

end Bosonic
end SecondQuantization
