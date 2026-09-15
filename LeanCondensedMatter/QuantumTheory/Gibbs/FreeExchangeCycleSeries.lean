import LeanCondensedMatter.Permutation.TraceLog
import LeanCondensedMatter.QuantumTheory.Gibbs.FreeBoltzmannKernel

set_option linter.style.header false

/-!
# Free thermal exchange-cycle series

The one-particle Boltzmann kernel is independent of second quantization, and the permutation
connected-cycle backend is already formulated for arbitrary exchange weight `ζ`. This file records
the corresponding Gibbs-level specialization once.

Everything here is formal. No evaluation of the power-series variable at `t = 1` is used.
-/

namespace QuantumTheory

variable {Mode : Type*} [Fintype Mode]

/-- For the diagonal free Boltzmann kernel and nonzero exchange weight `ζ`, the connected-cycle
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

end QuantumTheory
