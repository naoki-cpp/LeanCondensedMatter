import LeanCondensedMatter.QuantumTheory.LinearResponse.AdiabaticSwitching
import LeanCondensedMatter.QuantumTheory.LinearResponse.ResponseChannel
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

The module also applies the same finite-time phase directly to a neutral `ResponseChannel`, keeping
its retarded measured/source kernel and explicit observable-variation contact expectation together.
It names convergence in the observation-time variable `T → +∞` and remains independent of particle
statistics, Fock-space realizations, current operators, lattice geometry, and conductivity
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

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ResponseChannel

/-- Finite-observation-time adiabatic response of a neutral response channel.

The source value at the observation time has been factored out, so the retarded kernel carries the
lag phase `exp ((i ω - η) (T - s))` while the explicit observable variation contributes its
contact expectation at `T`. No stationarity or infinite-time limit is assumed. -/
noncomputable def finiteTimeAdiabaticResponse
    (channel : ResponseChannel H)
    (system : BoundedFreeSystem H) (expectation : NormalizedExpectation H)
    (ω η T : ℝ) : ℂ :=
  (∫ s in (0 : ℝ)..T,
      adiabaticFrequencyPhase ω η (T - s) *
        channel.retardedKernel system expectation T s) +
    channel.contactExpectation system expectation T

/-- A fixed-observable channel has no contact contribution, so its finite-time adiabatic response is
exactly the retarded measured/source transform. -/
@[simp]
theorem finiteTimeAdiabaticResponse_fixed
    (system : BoundedFreeSystem H) (expectation : NormalizedExpectation H)
    (measured source : H →L[ℂ] H) (ω η T : ℝ) :
    (fixed measured source).finiteTimeAdiabaticResponse system expectation ω η T =
      ∫ s in (0 : ℝ)..T,
        adiabaticFrequencyPhase ω η (T - s) *
          retardedSusceptibility system expectation measured source T s := by
  rw [finiteTimeAdiabaticResponse, fixed_contactExpectation]
  simp [retardedKernel, fixed]

end ResponseChannel

/-- Existence of the observation-time limit `T → +∞` at fixed values of all other parameters. -/
def HasInfiniteObservationTimeLimit
    (response : ℝ → ℂ) (value : ℂ) : Prop :=
  Filter.Tendsto response Filter.atTop (nhds value)

end
end LinearResponse
end QuantumTheory
