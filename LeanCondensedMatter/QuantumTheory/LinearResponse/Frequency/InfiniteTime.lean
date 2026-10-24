import LeanCondensedMatter.QuantumTheory.LinearResponse.Frequency.FiniteTime
import LeanCondensedMatter.QuantumTheory.LinearResponse.Frequency.Integrability
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option linter.style.header false

/-!
# Observation-time convergence of adiabatic response

This module owns the representation-independent half-infinite adiabatic transform of a scalar
causal kernel. At fixed frequency `ω` and switching rate `η`, it records

```text
∫₀ᵀ dτ exp ((i ω - η) τ) K(τ)
  ⟶ ∫_(0,∞) dτ exp ((i ω - η) τ) K(τ)
```

under an explicit Bochner-integrability hypothesis on the positive-lag kernel.

For bounded observables, this module also owns convergence of the finite causal observation
window to the fixed-positive-rate susceptibility, using automatic adiabatic integrability.

The layer is independent of particle statistics, Fock-space realizations, current operators,
lattice geometry, and conductivity normalization. Operator-specific sufficient conditions for
integrability remain in `Frequency.Integrability`; physical current realizations consume the generic
stationary `ResponseChannel` interface.
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

open Set MeasureTheory Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H)) (hbar : ℝ)

/-- The switched response observed only over the finite causal window `(0,T]`. -/
noncomputable def finiteTimeAdiabaticFrequencyDomainSusceptibility
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) (omega eta T : ℝ) : ℂ :=
  ∫ τ : ℝ in Ioc 0 T,
    adiabaticFrequencySusceptibilityIntegrand U hbar expectation A B omega eta τ

/-- Integrability of the switched integrand makes growing observation windows converge to its
causal whole-line transform. No sign condition on the rate is needed beyond integrability. -/
theorem tendsto_finiteTimeAdiabaticFrequencyDomainSusceptibility_atTop
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) (omega eta : ℝ)
    (hInt : Integrable
      (adiabaticFrequencySusceptibilityIntegrand U hbar expectation A B omega eta)) :
    Tendsto
      (fun T : ℝ =>
        finiteTimeAdiabaticFrequencyDomainSusceptibility U hbar
          expectation A B omega eta T)
      atTop
      (𝓝 (adiabaticFrequencyDomainSusceptibility U hbar
        expectation A B omega eta)) := by
  rw [adiabaticFrequencyDomainSusceptibility,
    integral_adiabaticFrequencySusceptibilityIntegrand_eq_Ioi_zero
      U hbar expectation A B omega eta]
  let f : ℝ → ℂ :=
    adiabaticFrequencySusceptibilityIntegrand U hbar expectation A B omega eta
  have hunion : (⋃ T : ℝ, Ioc (0 : ℝ) T) = Ioi 0 := by
    ext τ
    simp only [mem_iUnion, mem_Ioc, mem_Ioi]
    constructor
    · rintro ⟨T, hpos, _⟩
      exact hpos
    · intro hpos
      exact ⟨τ, hpos, le_rfl⟩
  have ht := tendsto_setIntegral_of_monotone
    (f := f) (μ := volume)
    (s := fun T : ℝ => Ioc 0 T)
    (fun _ => measurableSet_Ioc)
    (fun _ _ hab _ hx => ⟨hx.1, hx.2.trans hab⟩)
    (by
      rw [hunion]
      exact hInt.integrableOn)
  rw [hunion] at ht
  simpa [finiteTimeAdiabaticFrequencyDomainSusceptibility, f] using ht

/-- On the causal half-line the commutator lag transform equals the whole-line retarded
susceptibility. This is an identity of totalized integrals, not a regulator-removal limit. -/
theorem infiniteTimeAdiabaticTransform_commutator_eq_susceptibility
    (expectation : NormalizedExpectation H) (A B : H →L[ℂ] H) (ω η : ℝ) :
    infiniteTimeAdiabaticTransform
        (fun τ => commutatorSusceptibility U hbar
          expectation A B τ 0) ω η =
      adiabaticFrequencyDomainSusceptibility U hbar expectation A B ω η := by
  rw [infiniteTimeAdiabaticTransform, adiabaticFrequencyDomainSusceptibility,
    integral_adiabaticFrequencySusceptibilityIntegrand_eq_Ioi_zero
      U hbar expectation A B ω η]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro τ hτ
  rw [adiabaticFrequencySusceptibilityIntegrand,
    retardedTimeDifferenceKernel_eq_commutatorSusceptibility_of_nonneg
      U hbar expectation A B (le_of_lt hτ)]

namespace ResponseChannel

/-- Fixed-frequency, fixed-rate half-line lag transform of a channel, including its stationary
contact expectation. Its interpretation as an observation-time limit requires stationarity. -/
noncomputable def infiniteTimeAdiabaticResponse
    (channel : ResponseChannel H) (U : Multiplicative ℝ →* unitary (H →L[ℂ] H)) (hbar : ℝ)
    (expectation : NormalizedExpectation H) (ω η : ℝ) : ℂ :=
  infiniteTimeAdiabaticTransform
      (fun τ => commutatorSusceptibility U hbar expectation
        channel.measured channel.source τ 0) ω η +
    expectation channel.observableVariation

/-- Stationarity and integrability of the phase-weighted lag kernel give the observation-time
limit. No sign restriction on the switching rate is imposed beyond that integrability hypothesis. -/
theorem hasInfiniteObservationTimeLimit_finiteTimeAdiabaticResponse_of_stationary
    (channel : ResponseChannel H) (U : Multiplicative ℝ →* unitary (H →L[ℂ] H)) (hbar : ℝ)
    (expectation : NormalizedExpectation H)
    (hstationary : IsStationary U expectation) (ω η : ℝ)
    (hInt : AdiabaticLagIntegrable
      (fun τ => commutatorSusceptibility U hbar expectation
        channel.measured channel.source τ 0) ω η) :
    HasInfiniteObservationTimeLimit
      (channel.finiteTimeAdiabaticResponse U hbar expectation ω η)
      (channel.infiniteTimeAdiabaticResponse U hbar expectation ω η) := by
  have h := hasInfiniteObservationTimeLimit_finiteTimeAdiabaticTransform
    (fun τ => commutatorSusceptibility U hbar expectation
      channel.measured channel.source τ 0) ω η hInt
  unfold HasInfiniteObservationTimeLimit at h ⊢
  have hC : Tendsto (fun _ : ℝ => expectation channel.observableVariation)
      atTop (𝓝 (expectation channel.observableVariation)) := tendsto_const_nhds
  apply (h.add hC).congr'
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with T hT
  exact (channel.finiteTimeAdiabaticResponse_eq_stationaryLag
    U hbar expectation hstationary ω η hT).symm

/-- A measurable scalar channel kernel is integrable at positive switching rate, giving the
observation-time limit in a stationary state. Rate removal and volume limits remain separate. -/
theorem hasInfiniteObservationTimeLimit_finiteTimeAdiabaticResponse_of_stationary_pos
    (channel : ResponseChannel H) (U : Multiplicative ℝ →* unitary (H →L[ℂ] H)) (hbar : ℝ)
    (expectation : NormalizedExpectation H)
    (hstationary : IsStationary U expectation) (ω η : ℝ) (hη : 0 < η)
    (hMeas : Measurable
      (retardedTimeDifferenceKernel U hbar expectation channel.measured channel.source)) :
    HasInfiniteObservationTimeLimit
      (channel.finiteTimeAdiabaticResponse U hbar expectation ω η)
      (channel.infiniteTimeAdiabaticResponse U hbar expectation ω η) := by
  apply channel.hasInfiniteObservationTimeLimit_finiteTimeAdiabaticResponse_of_stationary
    U hbar expectation hstationary ω η
  have hInt : IntegrableOn
      (adiabaticFrequencySusceptibilityIntegrand U hbar expectation
        channel.measured channel.source ω η) (Ioi (0 : ℝ)) volume :=
    (adiabaticIntegrable_of_pos U hbar expectation
      channel.measured channel.source ω η hη hMeas).integrable.integrableOn
  apply hInt.congr_fun
  · intro τ hτ
    rw [adiabaticFrequencySusceptibilityIntegrand,
      retardedTimeDifferenceKernel_eq_commutatorSusceptibility_of_nonneg
        U hbar expectation channel.measured channel.source (le_of_lt hτ)]
  · exact measurableSet_Ioi

end ResponseChannel

end
end LinearResponse
end QuantumTheory
