import LeanCondensedMatter.QuantumTheory.LinearResponse.FiniteTimeAdiabatic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option linter.style.header false

/-!
# Infinite-time scalar adiabatic response

This module owns the representation-independent half-infinite adiabatic transform of a scalar
causal kernel. At fixed frequency `ω` and switching rate `η`, it records

```text
∫₀ᵀ dτ exp ((i ω - η) τ) K(τ)
  ⟶ ∫_(0,∞) dτ exp ((i ω - η) τ) K(τ)
```

under an explicit Bochner-integrability hypothesis on the positive-lag kernel.

The layer is independent of particle statistics, Fock-space realizations, current operators,
lattice geometry, and conductivity normalization. Operator-specific sufficient conditions for
integrability remain in `AdiabaticIntegrability`; directional-current specializations remain in
`SecondQuantization.Fermionic.Transport.InfiniteTimeFrequencyResponse`.
-/

namespace QuantumTheory
namespace LinearResponse

noncomputable section

/-- Explicit integrability hypothesis for an adiabatically weighted positive-lag scalar kernel. -/
def AdiabaticLagIntegrable (kernel : ℝ → ℂ) (ω η : ℝ) : Prop :=
  MeasureTheory.IntegrableOn
    (fun τ => adiabaticFrequencyPhase ω η τ * kernel τ)
    (Set.Ioi (0 : ℝ)) MeasureTheory.volume

/-- The half-infinite adiabatic transform at fixed frequency and switching rate. -/
noncomputable def infiniteTimeAdiabaticTransform
    (kernel : ℝ → ℂ) (ω η : ℝ) : ℂ :=
  ∫ τ in Set.Ioi (0 : ℝ), adiabaticFrequencyPhase ω η τ * kernel τ

/-- Integrability of the weighted positive-lag kernel is sufficient for the observation-time
limit of the finite-time adiabatic transform. -/
theorem hasInfiniteObservationTimeLimit_finiteTimeAdiabaticTransform
    (kernel : ℝ → ℂ) (ω η : ℝ)
    (hInt : AdiabaticLagIntegrable kernel ω η) :
    HasInfiniteObservationTimeLimit
      (finiteTimeAdiabaticTransform kernel ω η)
      (infiniteTimeAdiabaticTransform kernel ω η) := by
  unfold HasInfiniteObservationTimeLimit
  change Filter.Tendsto
    (fun T : ℝ => ∫ τ in (0 : ℝ)..T,
      adiabaticFrequencyPhase ω η τ * kernel τ)
    Filter.atTop
    (nhds (∫ τ in Set.Ioi (0 : ℝ),
      adiabaticFrequencyPhase ω η τ * kernel τ))
  exact MeasureTheory.intervalIntegral_tendsto_integral_Ioi
    (μ := MeasureTheory.volume)
    (f := fun τ : ℝ => adiabaticFrequencyPhase ω η τ * kernel τ)
    (b := fun T : ℝ => T) (0 : ℝ) hInt Filter.tendsto_id

end
end LinearResponse
end QuantumTheory
