import LeanCondensedMatter.QuantumTheory.Gibbs.FreeExchangeCycleSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreePartitionFunction
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option linter.style.header false

/-!
# Free-fermion connected-cycle and grand-partition series

The free-fermion formal grand product is the `ζ = -1` specialization of the shared Gibbs-level
Bose/Fermi backend. This module keeps the fermionic domain-facing names while delegating the formal
product, logarithm, and connected-cycle proof to that shared owner.

The ordinary finite determinant `det(1 + K)` remains a fermion-specific physical consumer boundary.
No formal power series is evaluated at `t = 1` here.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*}

/-- The finite free-fermion partition function is the determinant of `1 + K`, where `K` is the
shared diagonal one-particle Boltzmann kernel. Determinant appears only at this physical consumer
boundary; it is not a second exchange-statistics backend. -/
theorem freePartitionFunction_eq_det_one_add_freeBoltzmannModeKernel
    [LinearOrder Mode] [Fintype Mode] (ε : Mode → ℝ) (β : ℝ) :
    freePartitionFunction ε β =
      Matrix.det (1 + QuantumTheory.freeBoltzmannModeKernel ε β) := by
  classical
  rw [freePartitionFunction_eq_prod]
  have hdiag :
      (1 + QuantumTheory.freeBoltzmannModeKernel ε β : Matrix Mode Mode ℂ) =
        Matrix.diagonal (fun i => 1 + Complex.exp (-(β : ℂ) * (ε i : ℂ))) := by
    rw [QuantumTheory.freeBoltzmannModeKernel_eq_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  rw [hdiag, Matrix.det_diagonal]

/-- Formal finite-mode free-fermion grand-partition series
`𝒵_F(t) = ∏ᵢ (1 + exp(-β εᵢ) t)`. -/
noncomputable def freeGrandPartitionSeries [Fintype Mode]
    (ε : Mode → ℝ) (β : ℝ) : PowerSeries ℂ :=
  QuantumTheory.freeExchangeGrandPartitionSeries (-1 : ℂ) (Or.inr rfl) ε β

@[simp]
theorem constantCoeff_freeGrandPartitionSeries [Fintype Mode]
    (ε : Mode → ℝ) (β : ℝ) :
    PowerSeries.constantCoeff (freeGrandPartitionSeries ε β) = 1 := by
  unfold freeGrandPartitionSeries
  exact
    QuantumTheory.constantCoeff_freeExchangeGrandPartitionSeries
      (-1 : ℂ) (Or.inr rfl) ε β

/-- Free-fermion formal linked-cluster identity: the logarithm of the finite grand product equals the
`ζ = -1` connected-cycle series. -/
theorem logOf_freeGrandPartitionSeries_eq_permutationConnectedCycleSeries
    [Fintype Mode] (ε : Mode → ℝ) (β : ℝ) :
    PowerSeries.logOf (freeGrandPartitionSeries ε β) =
      Combinatorics.permutationConnectedCycleSeries (-1)
        (QuantumTheory.freeBoltzmannModeKernel ε β) := by
  unfold freeGrandPartitionSeries
  exact
    QuantumTheory.logOf_freeExchangeGrandPartitionSeries_eq_permutationConnectedCycleSeries
      (-1 : ℂ) (Or.inr rfl) ε β

end Fermionic
end SecondQuantization
