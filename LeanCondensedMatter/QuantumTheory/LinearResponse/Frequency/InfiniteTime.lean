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
  have ht := intervalIntegral_tendsto_integral_Ioi
    (μ := volume)
    (f := adiabaticFrequencySusceptibilityIntegrand U hbar expectation A B omega eta)
    (b := fun T : ℝ => T) (0 : ℝ) hInt.integrableOn tendsto_id
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  exact intervalIntegral.integral_of_le hT

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

/-- A bounded scalar kernel has a vanishing upper adiabatic boundary
at strictly positive switching rate. No decay of the kernel itself is assumed. -/
theorem tendsto_adiabaticFrequencyPhase_mul_of_bounded
    (K : ℝ → ℂ) (ω η : ℝ) (hη : 0 < η) (C : ℝ)
    (hK : ∀ t, ‖K t‖ ≤ C) :
    Tendsto (fun T : ℝ => adiabaticFrequencyPhase ω η T * K T) atTop (𝓝 0) := by
  have hneg : Tendsto (fun T : ℝ => -η * T) atTop atBot :=
    (tendsto_const_mul_atBot_of_neg (neg_lt_zero.mpr hη)).2 tendsto_id
  have hexp : Tendsto (fun T : ℝ => Real.exp (-η * T)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  have hupper : Tendsto (fun T : ℝ => Real.exp (-η * T) * C) atTop (𝓝 0) := by
    simpa only [zero_mul] using hexp.mul_const C
  apply (tendsto_zero_iff_norm_tendsto_zero).2
  refine squeeze_zero (fun T => norm_nonneg _) (fun T => ?_) hupper
  have hphase : ‖adiabaticFrequencyPhase ω η T‖ = Real.exp (-η * T) := by
    rw [adiabaticFrequencyPhase, Complex.norm_exp]
    simp [Complex.mul_re, Complex.sub_re, Complex.sub_im]
  rw [norm_mul, hphase]
  exact mul_le_mul_of_nonneg_left (hK T) (Real.exp_nonneg _)

/-- For bounded free dynamics, every commutator lag kernel is automatically
integrable at positive switching rate. -/
theorem adiabaticLagIntegrable_commutator_of_pos
    (system : BoundedFreeSystem H) (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) (ω η : ℝ) (hη : 0 < η) :
    AdiabaticLagIntegrable
      (fun τ => commutatorSusceptibility (freePropagatorGroup system)
        system.hbar expectation A B τ 0) ω η := by
  let U := freePropagatorGroup system
  have hMeas := measurable_retardedTimeDifferenceKernel U system.hbar expectation A B
    (continuous_commutatorSusceptibility_timeDifference U system.hbar expectation A B
      (continuous_heisenbergEvolution system A)).measurable
  have hInt : IntegrableOn
      (adiabaticFrequencySusceptibilityIntegrand U system.hbar expectation A B ω η)
      (Ioi (0 : ℝ)) volume :=
    (adiabaticIntegrable_of_pos U system.hbar expectation A B ω η hη hMeas).integrable.integrableOn
  apply hInt.congr_fun
  · intro τ hτ
    rw [adiabaticFrequencySusceptibilityIntegrand,
      retardedTimeDifferenceKernel_eq_commutatorSusceptibility_of_nonneg
        U system.hbar expectation A B (le_of_lt hτ)]
  · exact measurableSet_Ioi

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

/-- A stationary bounded response satisfying the finite displacement boundary
identity has a fixed-positive-rate infinite-time value equal to minus the
adiabatic exponent times the displacement susceptibility. This consumes
the finite-time identity, so model-level realizations do not have to repeat
their measured-operator and contact proofs. -/
theorem infiniteTimeAdiabaticResponse_eq_of_displacement_boundary
    (channel : ResponseChannel H) (system : BoundedFreeSystem H)
    (expectation : NormalizedExpectation H)
    (hstationary : IsStationary (freePropagatorGroup system) expectation)
    (D : H →L[ℂ] H) (ω η : ℝ) (hη : 0 < η)
    (hfinite : ∀ T : ℝ, 0 ≤ T →
      let K := fun τ => commutatorSusceptibility (freePropagatorGroup system)
        system.hbar expectation D channel.source τ 0
      channel.finiteTimeAdiabaticResponse (freePropagatorGroup system)
        system.hbar expectation ω η T =
        adiabaticFrequencyPhase ω η T * K T -
          (Complex.I * (ω : ℂ) - (η : ℂ)) *
            finiteTimeAdiabaticTransform K ω η T) :
    channel.infiniteTimeAdiabaticResponse (freePropagatorGroup system)
      system.hbar expectation ω η =
      -(Complex.I * (ω : ℂ) - (η : ℂ)) *
        adiabaticFrequencyDomainSusceptibility (freePropagatorGroup system)
          system.hbar expectation D channel.source ω η := by
  let U := freePropagatorGroup system
  let K := fun τ => commutatorSusceptibility U system.hbar expectation D channel.source τ 0
  let z := Complex.I * (ω : ℂ) - (η : ℂ)
  have hboundary : Tendsto (fun T : ℝ => adiabaticFrequencyPhase ω η T * K T)
      atTop (𝓝 0) :=
    tendsto_adiabaticFrequencyPhase_mul_of_bounded K ω η hη
      (retardedTimeDifferenceKernelNormBound system.hbar expectation D channel.source)
      (fun T => norm_commutatorSusceptibility_le U system.hbar expectation D channel.source T 0)
  have htransform := hasInfiniteObservationTimeLimit_finiteTimeAdiabaticTransform K ω η
    (adiabaticLagIntegrable_commutator_of_pos system expectation D channel.source ω η hη)
  unfold HasInfiniteObservationTimeLimit at htransform
  have hresponse := channel.hasInfiniteObservationTimeLimit_finiteTimeAdiabaticResponse_of_stationary
    U system.hbar expectation hstationary ω η
    (adiabaticLagIntegrable_commutator_of_pos system expectation
      channel.measured channel.source ω η hη)
  unfold HasInfiniteObservationTimeLimit at hresponse
  have hlimit : Tendsto
      (fun T => channel.finiteTimeAdiabaticResponse U system.hbar expectation ω η T)
      atTop (𝓝 (-(z * infiniteTimeAdiabaticTransform K ω η))) := by
    have h := hboundary.sub (htransform.const_mul z)
    rw [zero_sub] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact (hfinite T hT).symm
  have heq := tendsto_nhds_unique hresponse hlimit
  change channel.infiniteTimeAdiabaticResponse U system.hbar expectation ω η =
    -z * adiabaticFrequencyDomainSusceptibility U system.hbar expectation D channel.source ω η
  have hχ : infiniteTimeAdiabaticTransform K ω η =
      adiabaticFrequencyDomainSusceptibility U system.hbar expectation D channel.source ω η :=
    infiniteTimeAdiabaticTransform_commutator_eq_susceptibility
      U system.hbar expectation D channel.source ω η
  simpa only [hχ, neg_mul] using heq

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The full stationary response of a bounded displacement derivative, with
its physical source contact, is minus the adiabatic exponent times the
displacement susceptibility at positive switching rate. This is the
infinite-observation-time limit, not the zero-rate or DC limit. -/
theorem infiniteTimeAdiabaticResponse_of_displacement
    (channel : ResponseChannel H) (system : BoundedFreeSystem H)
    (expectation : NormalizedExpectation H)
    (hstationary : IsStationary (freePropagatorGroup system) expectation)
    (D : H →L[ℂ] H)
    (hJ : channel.measured =
      (Complex.I / (system.hbar : ℂ)) • ⁅system.hamiltonian.1, D⁆)
    (hC : channel.observableVariation =
      (Complex.I / (system.hbar : ℂ)) • ⁅-channel.source, D⁆)
    (ω η : ℝ) (hη : 0 < η) :
    channel.infiniteTimeAdiabaticResponse (freePropagatorGroup system)
      system.hbar expectation ω η =
      -(Complex.I * (ω : ℂ) - (η : ℂ)) *
        adiabaticFrequencyDomainSusceptibility (freePropagatorGroup system)
          system.hbar expectation D channel.source ω η :=
  channel.infiniteTimeAdiabaticResponse_eq_of_displacement_boundary system expectation
    hstationary D ω η hη (fun T hT =>
      channel.finiteTimeAdiabaticResponse_of_displacement system expectation
        hstationary D hJ hC ω η hT)

end ResponseChannel

end
end LinearResponse
end QuantumTheory
