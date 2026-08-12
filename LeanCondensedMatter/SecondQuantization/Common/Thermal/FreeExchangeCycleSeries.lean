import LeanCondensedMatter.Permutation
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FreeBoltzmannModeKernel

set_option linter.style.header false

/-!
# ζ-generic free thermal exchange-cycle series

The one-particle Boltzmann kernel is statistics-independent, and the permutation connected-cycle
backend is already formulated for arbitrary `ζ`. This file specializes that generic combinatorics to
the shared free Boltzmann kernel once. Fermionic `ζ = -1` and bosonic `ζ = +1` consumers should be
thin corollaries of these theorems rather than duplicate the diagonal trace-log proof.

Everything here is formal. No evaluation of the power-series variable at `t = 1` is used.
-/

namespace SecondQuantization
namespace Common

variable {Mode : Type*} [Fintype Mode]

/-- For the shared diagonal free Boltzmann kernel and nonzero exchange weight `ζ`, the connected-cycle
series is the modewise formal trace-log

`-(1/ζ) Σᵢ log(1 - ζ qᵢ t)`, where `qᵢ = exp(-β εᵢ)`. -/
theorem permutationConnectedCycleSeries_freeBoltzmannModeKernel_eq_sum_log
    (ζ : ℂ) (hζ : ζ ≠ 0) (ε : Mode → ℝ) (β : ℝ) :
    Combinatorics.permutationConnectedCycleSeries ζ (freeBoltzmannModeKernel ε β) =
      (-ζ⁻¹) • ∑ i : Mode,
        PowerSeries.rescale
          (-ζ * Complex.exp (-(β : ℂ) * (ε i : ℂ))) (PowerSeries.log ℂ) := by
  classical
  rw [freeBoltzmannModeKernel_eq_diagonal]
  simpa using
    (Combinatorics.permutationConnectedCycleSeries_diagonal_eq_neg_inv_smul_sum_log
      ζ (fun i : Mode => Complex.exp (-(β : ℂ) * (ε i : ℂ))) hζ)

/-- The logarithm of the `ζ`-generic formal grand-partition series for the shared free Boltzmann
kernel is the same modewise trace-log. -/
theorem logOf_permutationGrandPartitionSeries_freeBoltzmannModeKernel_eq_sum_log
    (ζ : ℂ) (hζ : ζ ≠ 0) (ε : Mode → ℝ) (β : ℝ) :
    PowerSeries.logOf
        (Combinatorics.permutationGrandPartitionSeries ζ (freeBoltzmannModeKernel ε β)) =
      (-ζ⁻¹) • ∑ i : Mode,
        PowerSeries.rescale
          (-ζ * Complex.exp (-(β : ℂ) * (ε i : ℂ))) (PowerSeries.log ℂ) := by
  rw [Combinatorics.logOf_permutationGrandPartitionSeries]
  exact permutationConnectedCycleSeries_freeBoltzmannModeKernel_eq_sum_log ζ hζ ε β

end Common
end SecondQuantization
