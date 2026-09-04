import LeanCondensedMatter.QuantumTheory.LinearResponse.AdiabaticSwitching
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option linter.style.header false

/-!
# Automatic integrability of fixed-rate adiabatic response

For bounded observables, free Heisenberg evolution is isometric because it is conjugation by a
unitary propagator. Consequently the retarded commutator kernel is uniformly bounded. Combining
that bound with the exponential factor `exp ((i ω - η) τ)` proves that every strictly positive
switching rate is Bochner integrable; no extra convergence assumption is needed at fixed `η > 0`.

The limit `η → 0⁺` remains a separate question and is not formed in this module.
-/

namespace QuantumTheory
namespace LinearResponse

open Set MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (system : BoundedFreeSystem H)

/-- Every free Schrödinger propagator is a unitary element of the bounded-operator C⋆-algebra. -/
theorem freePropagator_mem_unitary (t : ℝ) :
    freePropagator system t ∈ unitary (H →L[ℂ] H) := by
  rw [Unitary.mem_iff]
  constructor
  · rw [star_freePropagator, freePropagator_neg_mul]
  · rw [star_freePropagator, freePropagator_mul_neg]

/-- Unitary free conjugation preserves the operator norm exactly. -/
@[simp]
theorem norm_heisenbergEvolution (A : H →L[ℂ] H) (t : ℝ) :
    ‖heisenbergEvolution system A t‖ = ‖A‖ := by
  have hU := freePropagator_mem_unitary system t
  rw [heisenbergEvolution, ← star_freePropagator system t]
  calc
    ‖star (freePropagator system t) * A * freePropagator system t‖ =
        ‖star (freePropagator system t) * A‖ :=
      CStarRing.norm_mul_mem_unitary _ hU
    _ = ‖A‖ :=
      CStarRing.norm_mem_unitary_mul A (Unitary.star_mem hU)

/-- The free propagator depends continuously on real time in operator norm. -/
theorem continuous_freePropagator : Continuous (freePropagator system) := by
  have hcomplex : Continuous (fun z : ℂ =>
      NormedSpace.exp (z • schrodingerGenerator system)) :=
    (differentiable_exp_smul_const ℂ (schrodingerGenerator system)).continuous
  change Continuous
    ((fun z : ℂ => NormedSpace.exp (z • schrodingerGenerator system)) ∘
      Complex.ofReal)
  exact hcomplex.comp Complex.continuous_ofReal

/-- Free Heisenberg evolution of a fixed bounded observable is norm-continuous in time. -/
theorem continuous_heisenbergEvolution (A : H →L[ℂ] H) :
    Continuous (fun t : ℝ => heisenbergEvolution system A t) := by
  have hneg : Continuous (fun t : ℝ => freePropagator system (-t)) :=
    (continuous_freePropagator system).comp continuous_neg
  change Continuous
    (((fun t : ℝ => freePropagator system (-t)) * (fun _ : ℝ => A)) *
      freePropagator system)
  exact (hneg.mul continuous_const).mul (continuous_freePropagator system)

/-- The unswitched commutator kernel with source time fixed to zero is continuous. -/
theorem continuous_commutatorSusceptibility_timeDifference
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) :
    Continuous (fun τ : ℝ =>
      commutatorSusceptibility system expectation A B τ 0) := by
  have hA := continuous_heisenbergEvolution system A
  have hcomm : Continuous (fun τ : ℝ =>
      heisenbergEvolution system A τ * B -
        B * heisenbergEvolution system A τ) :=
    (hA.mul continuous_const).sub (continuous_const.mul hA)
  have hexpect : Continuous (fun τ : ℝ => expectation
      (heisenbergEvolution system A τ * B -
        B * heisenbergEvolution system A τ)) :=
    expectation.toContinuousLinearMap.continuous.comp hcomm
  convert
    ((continuous_const : Continuous (fun _ : ℝ => Complex.I / (system.hbar : ℂ))).mul hexpect)
    using 1
  funext τ
  simp only [Pi.mul_apply, commutatorSusceptibility, heisenbergEvolution_zero]

/-- The causal time-difference kernel is Borel measurable; its only possible jump is at zero. -/
theorem measurable_retardedTimeDifferenceKernel
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) :
    Measurable (retardedTimeDifferenceKernel system expectation A B) := by
  have hcomm :=
    (continuous_commutatorSusceptibility_timeDifference system expectation A B).measurable
  change Measurable (fun τ : ℝ =>
    if τ ∈ Ici (0 : ℝ) then
      commutatorSusceptibility system expectation A B τ 0
    else 0)
  exact Measurable.ite measurableSet_Ici hcomm measurable_const

/-- A uniform scalar bound for the causal bounded-operator kernel. -/
noncomputable def retardedTimeDifferenceKernelNormBound
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) : ℝ :=
  ‖Complex.I / (system.hbar : ℂ)‖ *
    ‖expectation.toContinuousLinearMap‖ *
      (2 * ‖A‖ * ‖B‖)

/-- The uniform kernel bound is nonnegative. -/
theorem retardedTimeDifferenceKernelNormBound_nonneg
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) :
    0 ≤ retardedTimeDifferenceKernelNormBound system expectation A B := by
  unfold retardedTimeDifferenceKernelNormBound
  exact mul_nonneg
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) (norm_nonneg _))

/-- Uniform norm control of the causal retarded kernel. -/
theorem norm_retardedTimeDifferenceKernel_le
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) (τ : ℝ) :
    ‖retardedTimeDifferenceKernel system expectation A B τ‖ ≤
      retardedTimeDifferenceKernelNormBound system expectation A B := by
  by_cases hτ : τ < 0
  · rw [retardedTimeDifferenceKernel_eq_zero_of_neg system expectation A B hτ, norm_zero]
    exact retardedTimeDifferenceKernelNormBound_nonneg system expectation A B
  · have hτnonneg : 0 ≤ τ := le_of_not_gt hτ
    rw [retardedTimeDifferenceKernel_eq_commutatorSusceptibility_of_nonneg
      system expectation A B hτnonneg]
    simp only [commutatorSusceptibility, heisenbergEvolution_zero]
    let X : H →L[ℂ] H :=
      heisenbergEvolution system A τ * B -
        B * heisenbergEvolution system A τ
    have hX : ‖X‖ ≤ 2 * ‖A‖ * ‖B‖ := by
      calc
        ‖X‖ ≤ ‖heisenbergEvolution system A τ * B‖ +
            ‖B * heisenbergEvolution system A τ‖ :=
          norm_sub_le _ _
        _ ≤ ‖heisenbergEvolution system A τ‖ * ‖B‖ +
            ‖B‖ * ‖heisenbergEvolution system A τ‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ = 2 * ‖A‖ * ‖B‖ := by
          rw [norm_heisenbergEvolution]
          ring
    have hexpect : ‖expectation X‖ ≤
        ‖expectation.toContinuousLinearMap‖ * ‖X‖ :=
      expectation.toContinuousLinearMap.le_opNorm X
    calc
      ‖(Complex.I / (system.hbar : ℂ)) * expectation X‖ =
          ‖Complex.I / (system.hbar : ℂ)‖ * ‖expectation X‖ :=
        norm_mul _ _
      _ ≤ ‖Complex.I / (system.hbar : ℂ)‖ *
          (‖expectation.toContinuousLinearMap‖ * ‖X‖) :=
        mul_le_mul_of_nonneg_left hexpect (norm_nonneg _)
      _ ≤ ‖Complex.I / (system.hbar : ℂ)‖ *
          (‖expectation.toContinuousLinearMap‖ * (2 * ‖A‖ * ‖B‖)) := by
        gcongr
      _ = retardedTimeDifferenceKernelNormBound system expectation A B := by
        rw [retardedTimeDifferenceKernelNormBound]
        ring

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

/-- Every strictly positive switching rate is automatically integrable for bounded observables. -/
theorem adiabaticIntegrable_of_pos
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) (ω η : ℝ) (hη : 0 < η) :
    AdiabaticIntegrable system expectation A B ω η := by
  classical
  refine ⟨hη, ?_⟩
  let C := retardedTimeDifferenceKernelNormBound system expectation A B
  let S : Set ℝ := Ioi (-1 : ℝ)
  have hphase : IntegrableOn (adiabaticFrequencyPhase ω η) S volume := by
    simpa [S] using integrableOn_adiabaticFrequencyPhase_Ioi ω η (-1) hη
  have hkernelMeas : AEStronglyMeasurable
      (retardedTimeDifferenceKernel system expectation A B)
      (volume.restrict S) :=
    (measurable_retardedTimeDifferenceKernel system expectation A B).aestronglyMeasurable
  have hkernelBound : ∀ᵐ τ ∂volume.restrict S,
      ‖retardedTimeDifferenceKernel system expectation A B τ‖ ≤ C :=
    Filter.Eventually.of_forall fun τ =>
      norm_retardedTimeDifferenceKernel_le system expectation A B τ
  have hprod : IntegrableOn (fun τ : ℝ =>
      retardedTimeDifferenceKernel system expectation A B τ *
        adiabaticFrequencyPhase ω η τ) S volume := by
    exact hphase.bdd_mul hkernelMeas hkernelBound
  have hintegrand : IntegrableOn
      (adiabaticFrequencySusceptibilityIntegrand system expectation A B ω η)
      S volume := by
    apply hprod.congr_fun
    · intro τ _
      rw [adiabaticFrequencySusceptibilityIntegrand]
      exact mul_comm _ _
    · exact measurableSet_Ioi
  have hpiece : Integrable
      (S.piecewise
        (adiabaticFrequencySusceptibilityIntegrand system expectation A B ω η)
        (fun _ : ℝ => (0 : ℂ))) volume :=
    Integrable.piecewise measurableSet_Ioi hintegrand integrableOn_zero
  refine hpiece.congr (Filter.Eventually.of_forall fun τ => ?_)
  by_cases hτ : τ ∈ S
  · simp [Set.piecewise, hτ]
  · have hnot : ¬ (-1 : ℝ) < τ := by
      simpa [S] using hτ
    have hle : τ ≤ -1 := le_of_not_gt hnot
    have hneg : τ < 0 := lt_of_le_of_lt hle (by norm_num)
    have hzero := adiabaticFrequencySusceptibilityIntegrand_eq_zero_of_neg
      system expectation A B ω η hneg
    simp [Set.piecewise, hτ, hzero]

/-- Causality reduces the fixed-rate frequency integrand to the open positive half-line. -/
theorem integral_adiabaticFrequencySusceptibilityIntegrand_eq_Ioi_zero
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) (omega eta : ℝ) :
    (∫ τ : ℝ,
        adiabaticFrequencySusceptibilityIntegrand system expectation A B omega eta τ) =
      ∫ τ : ℝ in Ioi 0,
        adiabaticFrequencySusceptibilityIntegrand system expectation A B omega eta τ := by
  calc
    (∫ τ : ℝ,
        adiabaticFrequencySusceptibilityIntegrand system expectation A B omega eta τ) =
      ∫ τ : ℝ,
        (Ici (0 : ℝ)).indicator
          (adiabaticFrequencySusceptibilityIntegrand system expectation A B omega eta) τ := by
      apply integral_congr_ae
      filter_upwards [] with τ
      by_cases hτ : τ ∈ Ici (0 : ℝ)
      · simp [hτ]
      · have hneg : τ < 0 := by simpa [Set.mem_Ici, not_le] using hτ
        have hzero := adiabaticFrequencySusceptibilityIntegrand_eq_zero_of_neg
          system expectation A B omega eta hneg
        simp [hτ, hzero]
    _ = ∫ τ : ℝ in Ici 0,
        adiabaticFrequencySusceptibilityIntegrand system expectation A B omega eta τ :=
      integral_indicator measurableSet_Ici
    _ = ∫ τ : ℝ in Ioi 0,
        adiabaticFrequencySusceptibilityIntegrand system expectation A B omega eta τ :=
      integral_Ici_eq_integral_Ioi

/-- Fixed-rate susceptibility requiring only the physical hypothesis `η > 0`.

The underlying explicit `AdiabaticIntegrable` proof is supplied by
`adiabaticIntegrable_of_pos`. -/
noncomputable def adiabaticFrequencyDomainSusceptibilityOfPositiveRate
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) (ω η : ℝ) (hη : 0 < η) : ℂ :=
  let rate : {η : ℝ // 0 < η} := ⟨η, hη⟩
  adiabaticFrequencyDomainSusceptibility system expectation A B ω rate.1

end
end LinearResponse
end QuantumTheory
