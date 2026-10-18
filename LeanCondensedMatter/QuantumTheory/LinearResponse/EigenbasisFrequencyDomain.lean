import LeanCondensedMatter.QuantumTheory.LinearResponse.EigenbasisTimeDomain
import Mathlib.MeasureTheory.Integral.DominatedConvergence

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

/-- One switched eigenbasis transition before imposing causal support.  The surrounding integral
is restricted to the causal half-line. -/
noncomputable def eigenbasisAdiabaticTransitionIntegrand
    (data : EnergyEigenbasisLehmannData system ι)
    (A B : H →L[ℂ] H) (omega eta : ℝ)
    (mn : ι × ι) (τ : ℝ) : ℂ :=
  adiabaticFrequencyPhase omega eta τ *
    eigenbasisTimeDomainTerm system data A B τ mn

/-- The switched integrand written directly from the canonical transition record. -/
theorem eigenbasisAdiabaticTransitionIntegrand_eq_transitionMode
    (data : EnergyEigenbasisLehmannData system ι)
    (A B : H →L[ℂ] H) (omega eta : ℝ)
    (mn : ι × ι) (τ : ℝ) :
    eigenbasisAdiabaticTransitionIntegrand system data A B omega eta mn τ =
      (eigenbasisTransitionData system data A B mn).weight *
        lehmannMode system.hbar omega eta
          (eigenbasisTransitionData system data A B mn).energyGap τ := by
  rw [eigenbasisAdiabaticTransitionIntegrand, eigenbasisTimeDomainTerm,
    LehmannTransitionData.timeTerm, adiabaticFrequencyPhase,
    lehmannMode, lehmannModeExponent]
  rw [show
      Complex.exp
          ((Complex.I * (omega : ℂ) - (eta : ℂ)) * (τ : ℂ)) *
          ((eigenbasisTransitionData system data A B mn).weight *
            Complex.exp
              (Complex.I *
                (((((eigenbasisTransitionData system data A B mn).energyGap * τ) /
                  system.hbar : ℝ)) : ℂ))) =
        (eigenbasisTransitionData system data A B mn).weight *
          (Complex.exp
              ((Complex.I * (omega : ℂ) - (eta : ℂ)) * (τ : ℂ)) *
            Complex.exp
              (Complex.I *
                (((((eigenbasisTransitionData system data A B mn).energyGap * τ) /
                  system.hbar : ℝ)) : ℂ))) by ring]
  rw [← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The causal integral of one switched transition is its canonical fixed-rate frequency term. -/
theorem integral_eigenbasisAdiabaticTransitionIntegrand_Ioi_zero
    (data : EnergyEigenbasisLehmannData system ι)
    (A B : H →L[ℂ] H) (omega eta : ℝ)
    (mn : ι × ι) (hη : 0 < eta) :
    (∫ τ : ℝ in Ioi 0,
      eigenbasisAdiabaticTransitionIntegrand system data A B omega eta mn τ) =
      (eigenbasisTransitionData system data A B mn).frequencyTerm omega eta := by
  rw [setIntegral_congr_fun measurableSet_Ioi fun τ _ =>
    eigenbasisAdiabaticTransitionIntegrand_eq_transitionMode
      system data A B omega eta mn τ]
  rw [integral_const_mul]
  rw [integral_lehmannMode_Ioi_zero_eq_resolvent
    system.hbar omega eta
      (eigenbasisTransitionData system data A B mn).energyGap hη]
  rfl

/-- Absolute summability of transition weights suffices to exchange the countable transition sum
with the causal fixed-positive-rate Bochner integral. -/
theorem integral_tsum_eigenbasisAdiabaticTransitionIntegrand_Ioi_zero
    [Countable ι]
    (data : EnergyEigenbasisLehmannData system ι)
    (A B : H →L[ℂ] H) (omega eta : ℝ) (hη : 0 < eta)
    (hsum : EigenbasisLehmannSummable system data A B) :
    (∫ τ : ℝ in Ioi 0,
      ∑' mn : ι × ι,
        eigenbasisAdiabaticTransitionIntegrand system data A B omega eta mn τ) =
      eigenbasisLehmannSeries system data A B omega eta := by
  have hInt : ∀ mn : ι × ι,
      IntegrableOn
        (eigenbasisAdiabaticTransitionIntegrand system data A B omega eta mn)
        (Ioi 0) volume := by
    intro mn
    have hmode := integrableOn_lehmannMode_Ioi_zero
      system.hbar omega eta
        (eigenbasisTransitionData system data A B mn).energyGap hη
    have hweighted : IntegrableOn (fun τ : ℝ =>
        (eigenbasisTransitionData system data A B mn).weight *
          lehmannMode system.hbar omega eta
            (eigenbasisTransitionData system data A B mn).energyGap τ) (Ioi 0) volume :=
      hmode.const_mul _
    apply hweighted.congr_fun
    · intro τ _
      exact (eigenbasisAdiabaticTransitionIntegrand_eq_transitionMode
        system data A B omega eta mn τ).symm
    · exact measurableSet_Ioi
  have hSum : Summable fun mn : ι × ι =>
      ∫ τ : ℝ in Ioi 0,
        ‖eigenbasisAdiabaticTransitionIntegrand system data A B omega eta mn τ‖ := by
    let C : ℝ := ∫ τ : ℝ in Ioi 0, ‖adiabaticFrequencyPhase omega eta τ‖
    apply (hsum.mul_left C).congr
    intro mn
    symm
    calc
      (∫ τ : ℝ in Ioi 0,
          ‖eigenbasisAdiabaticTransitionIntegrand system data A B omega eta mn τ‖) =
        ∫ τ : ℝ in Ioi 0,
          ‖(eigenbasisTransitionData system data A B mn).weight‖ *
            ‖adiabaticFrequencyPhase omega eta τ‖ := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro τ _
          simp [eigenbasisAdiabaticTransitionIntegrand,
            eigenbasisTimeDomainTerm]
          ring
      _ = ‖(eigenbasisTransitionData system data A B mn).weight‖ * C := by
        rw [integral_const_mul]
      _ = C * ‖(eigenbasisTransitionData system data A B mn).weight‖ := by ring
  rw [← MeasureTheory.integral_tsum_of_summable_integral_norm
    (μ := volume.restrict (Ioi 0)) hInt hSum]
  rw [eigenbasisLehmannSeries]
  apply tsum_congr
  intro mn
  exact integral_eigenbasisAdiabaticTransitionIntegrand_Ioi_zero
    system data A B omega eta mn hη

/-- The fixed-positive-rate physical susceptibility equals the countable eigenbasis Lehmann
resolvent series. -/
theorem adiabaticFrequencyDomainSusceptibilityOfPositiveRate_eigenbasis_eq_lehmannSeries
    [Countable ι]
    (data : EnergyEigenbasisLehmannData system ι)
    (A B : H →L[ℂ] H) (omega eta : ℝ) (hη : 0 < eta)
    (hsum : EigenbasisTimeDomainSummable system data A B) :
    adiabaticFrequencyDomainSusceptibilityOfPositiveRate system
        (eigenbasisNormalizedExpectation system data) A B omega eta hη =
      eigenbasisLehmannSeries system data A B omega eta := by
  rw [adiabaticFrequencyDomainSusceptibilityOfPositiveRate,
    adiabaticFrequencyDomainSusceptibility,
    integral_adiabaticFrequencySusceptibilityIntegrand_eq_Ioi_zero
      system (eigenbasisNormalizedExpectation system data) A B omega eta]
  calc
    (∫ τ : ℝ in Ioi 0,
        adiabaticFrequencySusceptibilityIntegrand system
          (eigenbasisNormalizedExpectation system data) A B omega eta τ) =
      ∫ τ : ℝ in Ioi 0,
        ∑' mn : ι × ι,
          eigenbasisAdiabaticTransitionIntegrand system data A B omega eta mn τ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro τ hτ
        rw [adiabaticFrequencySusceptibilityIntegrand]
        rw [retardedTimeDifferenceKernel_eigenbasis_eq_timeDomainSeries_of_nonneg
          system data A B (le_of_lt hτ) hsum]
        rw [eigenbasisTimeDomainSeries]
        simp only [eigenbasisAdiabaticTransitionIntegrand]
        rw [tsum_mul_left]
    _ = eigenbasisLehmannSeries system data A B omega eta :=
      integral_tsum_eigenbasisAdiabaticTransitionIntegrand_Ioi_zero
        system data A B omega eta hη (hsum.lehmannSummable system data A B)

/-- In finite dimension, the physical susceptibility is the conventional finite double Lehmann
sum. -/
theorem adiabaticFrequencyDomainSusceptibilityOfPositiveRate_eigenbasis_eq_finite_sum
    [Fintype ι]
    (data : EnergyEigenbasisLehmannData system ι)
    (A B : H →L[ℂ] H) (omega eta : ℝ) (hη : 0 < eta) :
    adiabaticFrequencyDomainSusceptibilityOfPositiveRate system
        (eigenbasisNormalizedExpectation system data) A B omega eta hη =
      ∑ mn : ι × ι,
        (eigenbasisTransitionData system data A B mn).frequencyTerm omega eta := by
  rw [adiabaticFrequencyDomainSusceptibilityOfPositiveRate_eigenbasis_eq_lehmannSeries
    system data A B omega eta hη
      (eigenbasisTimeDomainSummable_of_finite system data A B)]
  exact eigenbasisLehmannSeries_eq_finite_sum system data A B omega eta

end
end LinearResponse
end QuantumTheory
