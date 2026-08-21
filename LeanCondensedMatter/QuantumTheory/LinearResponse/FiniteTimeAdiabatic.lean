import LeanCondensedMatter.QuantumTheory.LinearResponse.AdiabaticSwitching
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option linter.style.header false

/-!
# Finite-time scalar adiabatic response

This module owns the representation-independent finite-observation-time transform used by the
frequency-domain response stack. For a scalar causal kernel `K` and the canonical adiabatic phase

```text
exp ((i ω - η) τ),
```

the finite-time transform is

```text
∫₀ᵀ dτ exp ((i ω - η) τ) K(τ).
```

The module also names convergence in the observation-time variable `T → +∞`. It is independent of
particle statistics, Fock-space realizations, current operators, lattice geometry, and conductivity
normalization. Zero-switching and static-limit orderings are owned separately by `LimitOrder`.
-/

namespace QuantumTheory
namespace LinearResponse

noncomputable section

/-- Finite-observation-time adiabatic transform of a scalar causal kernel. No limit is taken. -/
noncomputable def finiteTimeAdiabaticTransform
    (kernel : ℝ → ℂ) (ω η T : ℝ) : ℂ :=
  ∫ τ in (0 : ℝ)..T, adiabaticFrequencyPhase ω η τ * kernel τ

@[simp]
theorem finiteTimeAdiabaticTransform_zero_time
    (kernel : ℝ → ℂ) (ω η : ℝ) :
    finiteTimeAdiabaticTransform kernel ω η 0 = 0 := by
  simp [finiteTimeAdiabaticTransform]

/-- Existence of the observation-time limit `T → +∞` at fixed values of all other parameters. -/
def HasInfiniteObservationTimeLimit
    (response : ℝ → ℂ) (value : ℂ) : Prop :=
  Filter.Tendsto response Filter.atTop (nhds value)

end
end LinearResponse
end QuantumTheory
