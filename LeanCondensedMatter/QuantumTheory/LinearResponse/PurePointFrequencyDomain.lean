import LeanCondensedMatter.QuantumTheory.LinearResponse.PurePointTimeDomain
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option linter.style.header false

/-!
# Frequency-domain pure-point Lehmann representation

This module completes the fixed-positive-rate pure-point bridge.  On the causal half-line, the
switched susceptibility integrand is the countable sum of damped transition modes.  Absolute
transition-weight summability and the common exponential envelope justify exchanging that countable
sum with the Bochner time integral.

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

/-- One switched pure-point transition before imposing causal support.  The surrounding integral
is restricted to the causal half-line. -/
noncomputable def purePointAdiabaticTransitionIntegrand
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) (omega eta : ℝ)
    (mn : ι × ι) (τ : ℝ) : ℂ :=
  adiabaticFrequencyPhase omega eta τ *
    purePointTimeDomainTerm system data A B τ mn

/-- A switched transition is its spectral weight times the corresponding damped Lehmann mode. -/
theorem purePointAdiabaticTransitionIntegrand_eq_weight_mul_lehmannMode
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) (omega eta : ℝ)
    (mn : ι × ι) (τ : ℝ) :
    purePointAdiabaticTransitionIntegrand system data A B omega eta mn τ =
      purePointTransitionWeight system data A B mn *
        lehmannMode system.hbar omega eta
          (data.energy mn.1 - data.energy mn.2) τ := by
  rw [purePointAdiabaticTransitionIntegrand,
    purePointTimeDomainTerm_eq_exp_energyDifference,
    adiabaticFrequencyPhase, lehmannMode, lehmannModeExponent]
  rw [show
      Complex.exp
          ((Complex.I * (omega : ℂ) - (eta : ℂ)) * (τ : ℂ)) *
          (purePointTransitionWeight system data A B mn *
            Complex.exp
              (Complex.I *
                (((((data.energy mn.1 - data.energy mn.2) * τ) /
                  system.hbar : ℝ)) : ℂ))) =
        purePointTransitionWeight system data A B mn *
          (Complex.exp
              ((Complex.I * (omega : ℂ) - (eta : ℂ)) * (τ : ℂ)) *
            Complex.exp
              (Complex.I *
                (((((data.energy mn.1 - data.energy mn.2) * τ) /
                  system.hbar : ℝ)) : ℂ))) by ring]
  rw [← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The countable transition sum may be exchanged with the causal fixed-rate Bochner integral. -/
theorem integral_tsum_purePointAdiabaticTransitionIntegrand_Ioi_zero
    [Countable ι]
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) (omega eta : ℝ) (hη : 0 < eta)
    (hsum : PurePointTimeDomainSummable system data A B) :
    (∫ τ : ℝ in Ioi 0,
      ∑' mn : ι × ι,
        purePointAdiabaticTransitionIntegrand system data A B omega eta mn τ) =
      purePointLehmannSeries system data A B omega eta := by
  have hInt : ∀ mn : ι × ι,
      IntegrableOn
        (purePointAdiabaticTransitionIntegrand system data A B omega eta mn)
        (Ioi 0) volume := by
    intro mn
    have hmode := integrableOn_lehmannMode_Ioi_zero
      system.hbar omega eta (data.energy mn.1 - data.energy mn.2) hη
    have hweighted : IntegrableOn (fun τ : ℝ =>
        purePointTransitionWeight system data A B mn *
          lehmannMode system.hbar omega eta
            (data.energy mn.1 - data.energy mn.2) τ) (Ioi 0) volume :=
      hmode.const_mul _
    apply hweighted.congr_fun
    · intro τ _
      exact (purePointAdiabaticTransitionIntegrand_eq_weight_mul_lehmannMode
        system data A B omega eta mn τ).symm
    · exact measurableSet_Ioi
  have hSum : Summable fun mn : ι × ι =>
      ∫ τ : ℝ in Ioi 0,
        ‖purePointAdiabaticTransitionIntegrand system data A B omega eta mn τ‖ := by
    let C : ℝ := ∫ τ : ℝ in Ioi 0, ‖adiabaticFrequencyPhase omega eta τ‖
    have hweight : Summable fun mn : ι × ι =>
        ‖purePointTransitionWeight system data A B mn‖ := by
      simpa only [PurePointLehmannSummable] using hsum.2.2
    have hmajorant : Summable fun mn : ι × ι =>
        C * ‖purePointTransitionWeight system data A B mn‖ :=
      hweight.mul_left C
    refine Summable.of_norm_bounded hmajorant fun mn => ?_
    have hnonneg : 0 ≤ ∫ τ : ℝ in Ioi 0,
        ‖purePointAdiabaticTransitionIntegrand system data A B omega eta mn τ‖ :=
      integral_nonneg fun _ => norm_nonneg _
    rw [Real.norm_of_nonneg hnonneg]
    calc
      (∫ τ : ℝ in Ioi 0,
          ‖purePointAdiabaticTransitionIntegrand system data A B omega eta mn τ‖) =
        ∫ τ : ℝ in Ioi 0,
          ‖purePointTransitionWeight system data A B mn‖ *
            ‖adiabaticFrequencyPhase omega eta τ‖ := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro τ _
          simp [purePointAdiabaticTransitionIntegrand,
            purePointTimeDomainTerm]
          ring
      _ = ‖purePointTransitionWeight system data A B mn‖ * C := by
        rw [integral_const_mul]
      _ = C * ‖purePointTransitionWeight system data A B mn‖ := by ring
      _ ≤ C * ‖purePointTransitionWeight system data A B mn‖ := le_rfl
  rw [← MeasureTheory.integral_tsum_of_summable_integral_norm
    (μ := volume.restrict (Ioi 0)) hInt hSum]
  rw [purePointLehmannSeries]
  apply tsum_congr
  intro mn
  rw [setIntegral_congr_fun measurableSet_Ioi fun τ _ =>
    purePointAdiabaticTransitionIntegrand_eq_weight_mul_lehmannMode
      system data A B omega eta mn τ]
  rw [integral_const_mul]
  rw [integral_lehmannMode_Ioi_zero_eq_resolvent
    system.hbar omega eta (data.energy mn.1 - data.energy mn.2) hη]
  rfl

/-- The fixed-positive-rate physical susceptibility equals the countable pure-point Lehmann
resolvent series. -/
theorem adiabaticFrequencyDomainSusceptibilityOfPositiveRate_purePoint_eq_lehmannSeries
    [Countable ι]
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) (omega eta : ℝ) (hη : 0 < eta)
    (hsum : PurePointTimeDomainSummable system data A B) :
    adiabaticFrequencyDomainSusceptibilityOfPositiveRate system
        (purePointNormalizedExpectation system data) A B omega eta hη =
      purePointLehmannSeries system data A B omega eta := by
  rw [adiabaticFrequencyDomainSusceptibilityOfPositiveRate,
    adiabaticFrequencyDomainSusceptibility,
    integral_adiabaticFrequencySusceptibilityIntegrand_eq_Ioi_zero
      system (purePointNormalizedExpectation system data) A B omega eta]
  calc
    (∫ τ : ℝ in Ioi 0,
        adiabaticFrequencySusceptibilityIntegrand system
          (purePointNormalizedExpectation system data) A B omega eta τ) =
      ∫ τ : ℝ in Ioi 0,
        ∑' mn : ι × ι,
          purePointAdiabaticTransitionIntegrand system data A B omega eta mn τ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro τ hτ
        rw [adiabaticFrequencySusceptibilityIntegrand]
        rw [retardedTimeDifferenceKernel_purePoint_eq_timeDomainSeries_of_nonneg
          system data A B (le_of_lt hτ) hsum]
        rw [purePointTimeDomainSeries]
        simp only [purePointAdiabaticTransitionIntegrand]
        rw [tsum_mul_left]
    _ = purePointLehmannSeries system data A B omega eta :=
      integral_tsum_purePointAdiabaticTransitionIntegrand_Ioi_zero
        system data A B omega eta hη hsum

/-- In finite dimension, the physical susceptibility is the conventional finite double Lehmann
sum. -/
theorem adiabaticFrequencyDomainSusceptibilityOfPositiveRate_purePoint_eq_finite_sum
    [Fintype ι]
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) (omega eta : ℝ) (hη : 0 < eta) :
    adiabaticFrequencyDomainSusceptibilityOfPositiveRate system
        (purePointNormalizedExpectation system data) A B omega eta hη =
      ∑ mn : ι × ι,
        lehmannTerm system.hbar omega eta
          (data.energy mn.1 - data.energy mn.2)
          (purePointTransitionWeight system data A B mn) := by
  rw [adiabaticFrequencyDomainSusceptibilityOfPositiveRate_purePoint_eq_lehmannSeries
    system data A B omega eta hη
      (purePointTimeDomainSummable_of_finite system data A B)]
  exact purePointLehmannSeries_eq_finite_sum system data A B omega eta

end
end LinearResponse
end QuantumTheory
