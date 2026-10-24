import LeanCondensedMatter.QuantumTheory.LinearResponse.Frequency.AdiabaticSwitching
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option linter.style.header false

/-!
# Automatic integrability of fixed-rate adiabatic response

For bounded observables, free Heisenberg evolution is isometric because it is conjugation by a
unitary propagator. Consequently the retarded commutator kernel is uniformly bounded. Combining
that bound with the exponential factor `exp ((i ω - η) τ)` proves Bochner integrability at every
strictly positive switching rate, provided the scalar causal kernel is measurable. No bounded
generator or operator-norm continuity of observable orbits is assumed. The measurable-kernel
hypothesis is separate from the uniform bound and is not supplied by unitarity alone.

The limit `η → 0⁺` remains a separate question and is not formed in this module.
-/

namespace QuantumTheory
namespace LinearResponse

open Set MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H)) (hbar : ℝ)

/-- The causal extension of a measurable scalar commutator kernel is measurable. -/
theorem measurable_retardedTimeDifferenceKernel
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H)
    (hcomm : Measurable (fun τ : ℝ =>
      commutatorSusceptibility U hbar expectation A B τ 0)) :
    Measurable (retardedTimeDifferenceKernel U hbar expectation A B) := by
  change Measurable (fun τ : ℝ =>
    if τ ∈ Ici (0 : ℝ) then
      commutatorSusceptibility U hbar expectation A B τ 0
    else 0)
  exact Measurable.ite measurableSet_Ici hcomm measurable_const

/-- A uniform scalar bound for the causal bounded-operator kernel. -/
noncomputable def retardedTimeDifferenceKernelNormBound
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) : ℝ :=
  ‖Complex.I / (hbar : ℂ)‖ *
    ‖expectation.toContinuousLinearMap‖ *
      (2 * ‖A‖ * ‖B‖)

/-- The uniform kernel bound is nonnegative. -/
theorem retardedTimeDifferenceKernelNormBound_nonneg
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) :
    0 ≤ retardedTimeDifferenceKernelNormBound hbar expectation A B := by
  unfold retardedTimeDifferenceKernelNormBound
  exact mul_nonneg
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) (norm_nonneg _))

/-- Uniform norm control of the causal retarded kernel. -/
theorem norm_retardedTimeDifferenceKernel_le
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) (τ : ℝ) :
    ‖retardedTimeDifferenceKernel U hbar expectation A B τ‖ ≤
      retardedTimeDifferenceKernelNormBound hbar expectation A B := by
  by_cases hτ : τ < 0
  · rw [retardedTimeDifferenceKernel_eq_zero_of_neg U hbar expectation A B hτ, norm_zero]
    exact retardedTimeDifferenceKernelNormBound_nonneg hbar expectation A B
  · have hτnonneg : 0 ≤ τ := le_of_not_gt hτ
    rw [retardedTimeDifferenceKernel_eq_commutatorSusceptibility_of_nonneg
      U hbar expectation A B hτnonneg]
    exact norm_commutatorSusceptibility_le
      U hbar expectation A B τ 0

/-- The exponentially damped complex phase is integrable on every right half-line when `η > 0`. -/
theorem integrableOn_adiabaticFrequencyPhase_Ioi
    (ω η c : ℝ) (hη : 0 < η) :
    IntegrableOn (adiabaticFrequencyPhase ω η) (Ioi c) volume := by
  have hre : (Complex.I * (ω : ℂ) - (η : ℂ)).re < 0 := by
    simpa using hη
  change IntegrableOn (fun τ : ℝ =>
    Complex.exp ((Complex.I * (ω : ℂ) - (η : ℂ)) * (τ : ℂ)))
      (Ioi c) volume
  exact integrableOn_exp_mul_complex_Ioi hre c

/-- A measurable scalar kernel of bounded observables is integrable at positive switching rate. -/
theorem adiabaticIntegrable_of_pos
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) (ω η : ℝ) (hη : 0 < η)
    (hMeas : Measurable (retardedTimeDifferenceKernel U hbar expectation A B)) :
    AdiabaticIntegrable U hbar expectation A B ω η := by
  classical
  refine ⟨hη, ?_⟩
  let C := retardedTimeDifferenceKernelNormBound hbar expectation A B
  let S : Set ℝ := Ioi (-1 : ℝ)
  have hphase : IntegrableOn (adiabaticFrequencyPhase ω η) S volume := by
    simpa [S] using integrableOn_adiabaticFrequencyPhase_Ioi ω η (-1) hη
  have hkernelMeas : AEStronglyMeasurable
      (retardedTimeDifferenceKernel U hbar expectation A B)
      (volume.restrict S) :=
    hMeas.aestronglyMeasurable
  have hkernelBound : ∀ᵐ τ ∂volume.restrict S,
      ‖retardedTimeDifferenceKernel U hbar expectation A B τ‖ ≤ C :=
    Filter.Eventually.of_forall fun τ =>
      norm_retardedTimeDifferenceKernel_le U hbar expectation A B τ
  have hprod : IntegrableOn (fun τ : ℝ =>
      retardedTimeDifferenceKernel U hbar expectation A B τ *
        adiabaticFrequencyPhase ω η τ) S volume := by
    exact hphase.bdd_mul hkernelMeas hkernelBound
  have hintegrand : IntegrableOn
      (adiabaticFrequencySusceptibilityIntegrand U hbar expectation A B ω η)
      S volume := by
    apply hprod.congr_fun
    · intro τ _
      rw [adiabaticFrequencySusceptibilityIntegrand]
      exact mul_comm _ _
    · exact measurableSet_Ioi
  have hpiece : Integrable
      (S.piecewise
        (adiabaticFrequencySusceptibilityIntegrand U hbar expectation A B ω η)
        (fun _ : ℝ => (0 : ℂ))) volume :=
    Integrable.piecewise (measurableSet_Ioi : MeasurableSet S).nullMeasurableSet
      hintegrand integrableOn_zero
  refine hpiece.congr (Filter.Eventually.of_forall fun τ => ?_)
  by_cases hτ : τ ∈ S
  · simp [Set.piecewise, hτ]
  · have hnot : ¬ (-1 : ℝ) < τ := by
      simpa [S] using hτ
    have hle : τ ≤ -1 := le_of_not_gt hnot
    have hneg : τ < 0 := lt_of_le_of_lt hle (by norm_num)
    have hzero := adiabaticFrequencySusceptibilityIntegrand_eq_zero_of_neg
      U hbar expectation A B ω η hneg
    simp [Set.piecewise, hτ, hzero]

/-- Causality reduces the fixed-rate frequency integrand to the open positive half-line. -/
theorem integral_adiabaticFrequencySusceptibilityIntegrand_eq_Ioi_zero
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) (omega eta : ℝ) :
    (∫ τ : ℝ,
        adiabaticFrequencySusceptibilityIntegrand U hbar expectation A B omega eta τ) =
      ∫ τ : ℝ in Ioi 0,
        adiabaticFrequencySusceptibilityIntegrand U hbar expectation A B omega eta τ := by
  calc
    (∫ τ : ℝ,
        adiabaticFrequencySusceptibilityIntegrand U hbar expectation A B omega eta τ) =
      ∫ τ : ℝ,
        (Ici (0 : ℝ)).indicator
          (adiabaticFrequencySusceptibilityIntegrand U hbar expectation A B omega eta) τ := by
      apply integral_congr_ae
      filter_upwards [] with τ
      by_cases hτ : τ ∈ Ici (0 : ℝ)
      · simp [hτ]
      · have hneg : τ < 0 := by simpa [Set.mem_Ici, not_le] using hτ
        have hzero := adiabaticFrequencySusceptibilityIntegrand_eq_zero_of_neg
          U hbar expectation A B omega eta hneg
        simp [hτ, hzero]
    _ = ∫ τ : ℝ in Ici 0,
        adiabaticFrequencySusceptibilityIntegrand U hbar expectation A B omega eta τ :=
      integral_indicator measurableSet_Ici
    _ = ∫ τ : ℝ in Ioi 0,
        adiabaticFrequencySusceptibilityIntegrand U hbar expectation A B omega eta τ :=
      integral_Ici_eq_integral_Ioi

end
end LinearResponse
end QuantumTheory
