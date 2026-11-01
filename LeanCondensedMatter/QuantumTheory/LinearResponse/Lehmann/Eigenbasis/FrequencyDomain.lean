import LeanCondensedMatter.QuantumTheory.LinearResponse.Lehmann.Transition
import LeanCondensedMatter.QuantumTheory.LinearResponse.Lehmann.Eigenbasis.TimeDomain
import LeanCondensedMatter.QuantumTheory.LinearResponse.Frequency.Integrability

set_option linter.style.header false

/-!
# Frequency-domain eigenbasis Lehmann representation

This module completes the fixed-positive-rate eigenbasis bridge.  On the causal half-line, the
switched susceptibility integrand is the countable sum of damped modes obtained from the same
`LehmannTransitionData` records as the time-domain series.  Absolute transition-weight summability
and the common exponential envelope justify exchanging that countable sum with the Bochner time
integral.

For `η > 0`, the resulting identity is

`χᴿ_AB(ω,η) = ∑' (m,n), Wₘₙ / (η - i(ω + (Eₘ-Eₙ)/ℏ))`,

where `Wₘₙ = (i/ℏ)(pₘ-pₙ)AₘₙBₙₘ`.  The finite-dimensional theorem is an immediate finite-sum
corollary.  No `η → 0⁺`, `ω → 0`, or long-time limit is formed here.
-/

namespace QuantumTheory
namespace LinearResponse

open Set MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}
variable (system : BoundedFreeSystem H)

/-- The fixed-positive-rate physical susceptibility equals the countable eigenbasis Lehmann
resolvent series. -/
theorem adiabaticFrequencyDomainSusceptibility_eigenbasis_eq_lehmannSeries
    [Countable ι]
    (data : EnergyEigenbasisLehmannData system ι)
    (A B : H →L[ℂ] H) (omega eta : ℝ) (hη : 0 < eta)
    (hsum : EigenbasisTimeDomainSummable system data A B) :
    adiabaticFrequencyDomainSusceptibility (freePropagatorGroup system) system.hbar
        (eigenbasisNormalizedExpectation system data) A B omega eta =
      eigenbasisLehmannSeries system data A B omega eta := by
  rw [adiabaticFrequencyDomainSusceptibility,
    integral_adiabaticFrequencySusceptibilityIntegrand_eq_Ioi_zero
      (freePropagatorGroup system) system.hbar
      (eigenbasisNormalizedExpectation system data) A B omega eta]
  calc
    (∫ τ : ℝ in Ioi 0,
        adiabaticFrequencySusceptibilityIntegrand (freePropagatorGroup system) system.hbar
          (eigenbasisNormalizedExpectation system data) A B omega eta τ) =
      ∫ τ : ℝ in Ioi 0,
        ∑' mn : ι × ι,
          (eigenbasisTransitionData system data A B mn).adiabaticTimeTerm omega eta τ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro τ hτ
        rw [adiabaticFrequencySusceptibilityIntegrand]
        rw [retardedTimeDifferenceKernel_eigenbasis_eq_timeDomainSeries_of_nonneg
          system data A B (le_of_lt hτ) hsum]
        rw [eigenbasisTimeDomainSeries]
        simp only [LehmannTransitionData.adiabaticTimeTerm,
          adiabaticFrequencyPhase, eigenbasisTimeDomainTerm]
        rw [tsum_mul_left]
    _ = eigenbasisLehmannSeries system data A B omega eta := by
      simpa only [eigenbasisLehmannSeries] using
        LehmannTransitionData.integral_tsum_adiabaticTimeTerm_Ioi_zero
          (eigenbasisTransitionData system data A B) omega eta hη
          (hsum.lehmannSummable system data A B)

/-- In finite dimension, the physical susceptibility is the conventional finite double Lehmann
sum. -/
theorem adiabaticFrequencyDomainSusceptibility_eigenbasis_eq_finite_sum
    [Fintype ι]
    (data : EnergyEigenbasisLehmannData system ι)
    (A B : H →L[ℂ] H) (omega eta : ℝ) (hη : 0 < eta) :
    adiabaticFrequencyDomainSusceptibility (freePropagatorGroup system) system.hbar
        (eigenbasisNormalizedExpectation system data) A B omega eta =
      ∑ mn : ι × ι,
        (eigenbasisTransitionData system data A B mn).frequencyTerm omega eta := by
  rw [adiabaticFrequencyDomainSusceptibility_eigenbasis_eq_lehmannSeries
    system data A B omega eta hη
      (eigenbasisTimeDomainSummable_of_finite system data A B)]
  exact eigenbasisLehmannSeries_eq_finite_sum system data A B omega eta

end
end LinearResponse
end QuantumTheory
