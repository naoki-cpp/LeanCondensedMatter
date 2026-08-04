import LeanCondensedMatter.QuantumTheory.LinearResponse.FrequencyDomain

set_option linter.style.header false

/-!
# Fixed-rate adiabatic switching for retarded susceptibility

This module keeps the adiabatically switched transform separate from the unswitched Fourier
transform.  For a real frequency `ω` and switching rate `η`, the phase convention is

`exp ((i ω - η) τ)`

and the fixed-rate transform is

`χᴿ_AB(ω, η) = ∫ τ : ℝ, exp ((i ω - η) τ) χᴿ_AB(τ)`.

The named predicate `AdiabaticIntegrable` includes both the physical condition `η > 0` and
Bochner integrability of the switched integrand.  No limit `η → 0⁺` is formed or assumed here.
The zero-rate integrand is related explicitly to the unswitched convention from `FrequencyDomain`.
-/

namespace QuantumTheory
namespace LinearResponse

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (system : BoundedFreeSystem H)

/-- The fixed-rate adiabatic phase `exp ((i ω - η) τ)`. -/
noncomputable def adiabaticFrequencyPhase (ω η τ : ℝ) : ℂ :=
  Complex.exp ((Complex.I * (ω : ℂ) - (η : ℂ)) * (τ : ℂ))

@[simp]
theorem adiabaticFrequencyPhase_zero_time (ω η : ℝ) :
    adiabaticFrequencyPhase ω η 0 = 1 := by
  simp [adiabaticFrequencyPhase]

@[simp]
theorem adiabaticFrequencyPhase_zero_rate (ω τ : ℝ) :
    adiabaticFrequencyPhase ω 0 τ = frequencyPhase ω τ := by
  simp [adiabaticFrequencyPhase, frequencyPhase]

@[simp]
theorem adiabaticFrequencyPhase_zero_frequency (η τ : ℝ) :
    adiabaticFrequencyPhase 0 η τ =
      Complex.exp (-(η : ℂ) * (τ : ℂ)) := by
  simp [adiabaticFrequencyPhase]

/-- The switched oscillatory integrand `exp ((i ω - η) τ) χᴿ_AB(τ)`. -/
noncomputable def adiabaticFrequencySusceptibilityIntegrand
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) (ω η τ : ℝ) : ℂ :=
  adiabaticFrequencyPhase ω η τ *
    retardedTimeDifferenceKernel system expectation A B τ

@[simp]
theorem adiabaticFrequencySusceptibilityIntegrand_eq_zero_of_neg
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) (ω η : ℝ) {τ : ℝ} (hτ : τ < 0) :
    adiabaticFrequencySusceptibilityIntegrand system expectation A B ω η τ = 0 := by
  simp [adiabaticFrequencySusceptibilityIntegrand,
    retardedTimeDifferenceKernel_eq_zero_of_neg system expectation A B hτ]

@[simp]
theorem adiabaticFrequencySusceptibilityIntegrand_zero_rate
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) (ω τ : ℝ) :
    adiabaticFrequencySusceptibilityIntegrand system expectation A B ω 0 τ =
      frequencySusceptibilityIntegrand system expectation A B ω τ := by
  simp [adiabaticFrequencySusceptibilityIntegrand,
    frequencySusceptibilityIntegrand]

@[simp]
theorem adiabaticFrequencySusceptibilityIntegrand_zero_frequency
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) (η τ : ℝ) :
    adiabaticFrequencySusceptibilityIntegrand system expectation A B 0 η τ =
      Complex.exp (-(η : ℂ) * (τ : ℂ)) *
        retardedTimeDifferenceKernel system expectation A B τ := by
  simp [adiabaticFrequencySusceptibilityIntegrand]

/-- Explicit assumptions for a physically adiabatic fixed-rate transform. -/
def AdiabaticIntegrable
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) (ω η : ℝ) : Prop :=
  0 < η ∧ MeasureTheory.Integrable
    (adiabaticFrequencySusceptibilityIntegrand system expectation A B ω η)

/-- Positivity of the switching rate carried by `AdiabaticIntegrable`. -/
theorem AdiabaticIntegrable.rate_pos
    {expectation : NormalizedExpectation H}
    {A B : H →L[ℂ] H} {ω η : ℝ}
    (hInt : AdiabaticIntegrable system expectation A B ω η) :
    0 < η :=
  hInt.1

/-- Integrability of the switched kernel carried by `AdiabaticIntegrable`. -/
theorem AdiabaticIntegrable.integrable
    {expectation : NormalizedExpectation H}
    {A B : H →L[ℂ] H} {ω η : ℝ}
    (hInt : AdiabaticIntegrable system expectation A B ω η) :
    MeasureTheory.Integrable
      (adiabaticFrequencySusceptibilityIntegrand system expectation A B ω η) :=
  hInt.2

/-- A zero switching rate is not an adiabatic rate. -/
@[simp]
theorem not_adiabaticIntegrable_zero_rate
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) (ω : ℝ) :
    ¬ AdiabaticIntegrable system expectation A B ω 0 := by
  simp [AdiabaticIntegrable]

/-- Totalized fixed-rate adiabatically switched retarded susceptibility.  Theorems using
convergence carry `AdiabaticIntegrable` explicitly. -/
noncomputable def adiabaticFrequencyDomainSusceptibility
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) (ω η : ℝ) : ℂ :=
  ∫ τ : ℝ,
    adiabaticFrequencySusceptibilityIntegrand system expectation A B ω η τ

/-- At zero frequency, only the exponential damping remains. -/
theorem adiabaticFrequencyDomainSusceptibility_zero_frequency
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) (η : ℝ) :
    adiabaticFrequencyDomainSusceptibility system expectation A B 0 η =
      ∫ τ : ℝ,
        Complex.exp (-(η : ℂ) * (τ : ℂ)) *
          retardedTimeDifferenceKernel system expectation A B τ := by
  simp [adiabaticFrequencyDomainSusceptibility,
    adiabaticFrequencySusceptibilityIntegrand]

/-- At zero switching rate, the totalized switched integral is exactly the unswitched transform.
This is an identity at fixed rate, not a statement about the limit `η → 0⁺`. -/
theorem integral_adiabaticFrequencySusceptibilityIntegrand_zero_rate_eq_frequencyDomain
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) (ω : ℝ) :
    (∫ τ : ℝ,
        adiabaticFrequencySusceptibilityIntegrand system expectation A B ω 0 τ) =
      frequencyDomainSusceptibility system expectation A B ω := by
  simp [frequencyDomainSusceptibility]

end
end LinearResponse
end QuantumTheory
