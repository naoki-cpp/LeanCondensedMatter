import LeanCondensedMatter.QuantumTheory.LinearResponse.FiniteTimeAdiabatic
import LeanCondensedMatter.QuantumTheory.LinearResponse.AdiabaticIntegrability
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

open Set MeasureTheory Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (system : BoundedFreeSystem H)

/-- The switched response observed only over the finite causal window `(0,T]`. -/
noncomputable def finiteTimeAdiabaticFrequencyDomainSusceptibility
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) (omega eta T : ℝ) : ℂ :=
  ∫ τ : ℝ in Ioc 0 T,
    adiabaticFrequencySusceptibilityIntegrand system expectation A B omega eta τ

/-- The same fixed-rate transform written directly as an integral over the open causal half-line. -/
noncomputable def causalAdiabaticFrequencyDomainSusceptibility
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) (omega eta : ℝ) : ℂ :=
  ∫ τ : ℝ in Ioi 0,
    adiabaticFrequencySusceptibilityIntegrand system expectation A B omega eta τ

/-- Causality reduces the full-real-line fixed-rate transform to the positive half-line. -/
theorem adiabaticFrequencyDomainSusceptibilityOfPositiveRate_eq_causal
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) (omega eta : ℝ) (hη : 0 < eta) :
    adiabaticFrequencyDomainSusceptibilityOfPositiveRate system
        expectation A B omega eta hη =
      causalAdiabaticFrequencyDomainSusceptibility system
        expectation A B omega eta := by
  rw [adiabaticFrequencyDomainSusceptibilityOfPositiveRate,
    adiabaticFrequencyDomainSusceptibility,
    causalAdiabaticFrequencyDomainSusceptibility]
  exact integral_adiabaticFrequencySusceptibilityIntegrand_eq_Ioi_zero
    system expectation A B omega eta

/-- At fixed frequency and fixed positive switching rate, increasing the observation window to
infinity converges to the causal fixed-rate transform. -/
theorem tendsto_finiteTimeAdiabaticFrequencyDomainSusceptibility_atTop
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) (omega eta : ℝ) (hη : 0 < eta) :
    Tendsto
      (fun T : ℝ =>
        finiteTimeAdiabaticFrequencyDomainSusceptibility system
          expectation A B omega eta T)
      atTop
      (𝓝 (causalAdiabaticFrequencyDomainSusceptibility system
        expectation A B omega eta)) := by
  let f : ℝ → ℂ :=
    adiabaticFrequencySusceptibilityIntegrand system expectation A B omega eta
  have hInt : Integrable f :=
    (adiabaticIntegrable_of_pos system expectation A B omega eta hη).integrable
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
  simpa [finiteTimeAdiabaticFrequencyDomainSusceptibility,
    causalAdiabaticFrequencyDomainSusceptibility, f] using ht

/-- The physical fixed-rate susceptibility is therefore obtained by taking `T → ∞` first, while
`omega` and the positive rate `eta` remain fixed. -/
theorem tendsto_finiteTimeAdiabaticFrequencyDomainSusceptibility_atTop_eq_fixedRate
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) (omega eta : ℝ) (hη : 0 < eta) :
    Tendsto
      (fun T : ℝ =>
        finiteTimeAdiabaticFrequencyDomainSusceptibility system
          expectation A B omega eta T)
      atTop
      (𝓝 (adiabaticFrequencyDomainSusceptibilityOfPositiveRate system
        expectation A B omega eta hη)) := by
  rw [adiabaticFrequencyDomainSusceptibilityOfPositiveRate_eq_causal
    system expectation A B omega eta hη]
  exact tendsto_finiteTimeAdiabaticFrequencyDomainSusceptibility_atTop
    system expectation A B omega eta hη


end
end LinearResponse
end QuantumTheory
