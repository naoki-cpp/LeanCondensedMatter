import LeanCondensedMatter.QuantumTheory.LinearResponse.RetardedSusceptibility

set_option linter.style.header false

/-!
# Frequency-domain retarded susceptibility

This module extracts the causal time-difference kernel

`χᴿ_AB(τ) = χᴿ_AB(τ, 0)`

from the two-time retarded susceptibility.  Under stationarity, the full two-time kernel is recovered
as `χᴿ_AB(t, s) = χᴿ_AB(t - s)`.

The frequency-domain convention is

`χᴿ_AB(ω) = ∫ τ : ℝ, exp (i ω τ) χᴿ_AB(τ)`.

Because the time-difference kernel vanishes for `τ < 0`, this is the one-sided transform usually
written as an integral over `[0, ∞)`.  Integrability is not hidden: the transform takes an explicit
proof of the named predicate `FrequencyIntegrable`.  No switching parameter, long-time limit, or
`η → 0` prescription is introduced in this module.
-/

namespace QuantumTheory
namespace LinearResponse

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (system : BoundedFreeSystem H)

/-- The causal one-time-difference kernel obtained by fixing the source time to zero. -/
noncomputable def retardedTimeDifferenceKernel
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) (τ : ℝ) : ℂ :=
  retardedSusceptibility system expectation A B τ 0

@[simp]
theorem retardedTimeDifferenceKernel_eq_zero_of_neg
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) {τ : ℝ} (hτ : τ < 0) :
    retardedTimeDifferenceKernel system expectation A B τ = 0 := by
  simpa [retardedTimeDifferenceKernel] using
    (retardedSusceptibility_eq_zero_of_lt system expectation A B hτ)

@[simp]
theorem retardedTimeDifferenceKernel_eq_commutatorSusceptibility_of_nonneg
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) {τ : ℝ} (hτ : 0 ≤ τ) :
    retardedTimeDifferenceKernel system expectation A B τ =
      commutatorSusceptibility system expectation A B τ 0 := by
  simp [retardedTimeDifferenceKernel, retardedSusceptibility, hτ]

/-- A stationary expectation makes the full retarded susceptibility a function only of `t - s`. -/
theorem retardedSusceptibility_eq_retardedTimeDifferenceKernel_of_stationary
    (expectation : NormalizedExpectation H)
    (hstationary : IsStationary system expectation)
    (A B : H →L[ℂ] H) (t s : ℝ) :
    retardedSusceptibility system expectation A B t s =
      retardedTimeDifferenceKernel system expectation A B (t - s) := by
  simpa [retardedTimeDifferenceKernel, retardedSusceptibility] using
    (retardedSusceptibility_eq_timeDifference_of_stationary
      system expectation hstationary A B t s)

/-- Fourier phase convention `exp (i ω τ)`. -/
noncomputable def frequencyPhase (ω τ : ℝ) : ℂ :=
  Complex.exp (Complex.I * (ω : ℂ) * (τ : ℂ))

@[simp]
theorem frequencyPhase_zero_frequency (τ : ℝ) :
    frequencyPhase 0 τ = 1 := by
  simp [frequencyPhase]

@[simp]
theorem frequencyPhase_zero_time (ω : ℝ) :
    frequencyPhase ω 0 = 1 := by
  simp [frequencyPhase]

/-- The oscillatory integrand defining the frequency-domain retarded susceptibility. -/
noncomputable def frequencySusceptibilityIntegrand
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) (ω τ : ℝ) : ℂ :=
  frequencyPhase ω τ * retardedTimeDifferenceKernel system expectation A B τ

@[simp]
theorem frequencySusceptibilityIntegrand_eq_zero_of_neg
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) (ω : ℝ) {τ : ℝ} (hτ : τ < 0) :
    frequencySusceptibilityIntegrand system expectation A B ω τ = 0 := by
  simp [frequencySusceptibilityIntegrand,
    retardedTimeDifferenceKernel_eq_zero_of_neg system expectation A B hτ]

@[simp]
theorem frequencySusceptibilityIntegrand_zero_frequency
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) (τ : ℝ) :
    frequencySusceptibilityIntegrand system expectation A B 0 τ =
      retardedTimeDifferenceKernel system expectation A B τ := by
  simp [frequencySusceptibilityIntegrand]

/-- Explicit integrability condition for the oscillatory susceptibility integrand. -/
def FrequencyIntegrable
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) (ω : ℝ) : Prop :=
  MeasureTheory.Integrable
    (frequencySusceptibilityIntegrand system expectation A B ω)

/-- Frequency-domain retarded susceptibility with convention `exp (i ω τ)`.

The proof argument makes the required Bochner integrability assumption explicit. -/
noncomputable def frequencyDomainSusceptibility
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) (ω : ℝ)
    (_hInt : FrequencyIntegrable system expectation A B ω) : ℂ :=
  ∫ τ : ℝ, frequencySusceptibilityIntegrand system expectation A B ω τ

/-- At zero frequency, the transform is the integral of the causal time-difference kernel. -/
theorem frequencyDomainSusceptibility_zero_frequency
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H)
    (hInt : FrequencyIntegrable system expectation A B 0) :
    frequencyDomainSusceptibility system expectation A B 0 hInt =
      ∫ τ : ℝ, retardedTimeDifferenceKernel system expectation A B τ := by
  simp [frequencyDomainSusceptibility, frequencySusceptibilityIntegrand]

end
end LinearResponse
end QuantumTheory
