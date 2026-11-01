import LeanCondensedMatter.QuantumTheory.LinearResponse.Dynamics.Stationarity
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Lie.OfAssociative

set_option linter.style.header false

/-!
# Retarded susceptibility for unitary-group dynamics

This module names the two-time commutator kernel underlying the source-coupled Kubo formula and
extends it by zero outside the causal region `s ≤ t`.

For an ordinary normalized expectation `ω`,

`χ_AB(t,s) = (i / ℏ) ω(A_I(t) B_I(s) - B_I(s) A_I(t))`

and

`χᴿ_AB(t,s) = if s ≤ t then χ_AB(t,s) else 0`.

Linearity in the measured observable is packaged here independently of perturbative derivation.
The source response is the causal convolution `∫₀ᵗ f(s) χᴿ_AB(t,s) ds`. Under stationarity, the
two-time kernel is reduced to a function of the time difference without adding a separate
correlation-function invariance axiom.

The propagator group and the real time-scale parameter `hbar` are supplied independently.
The algebraic formulas require neither a bounded generator nor continuity. Physical applications
supply `hbar > 0` and the correspondingly scaled propagators. Continuity of the scalar kernel is
derived here from an explicit norm-continuous observable orbit; strong continuity of the
propagators alone is not asserted to imply that hypothesis. Integral expressions are Mathlib's
totalized integrals; their physical interpretation requires separate integrability assumptions.
-/

namespace QuantumTheory
namespace LinearResponse

attribute [local instance 100] LieRing.ofAssociativeRing

open Set

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H)) (hbar : ℝ)

/-- The two-time commutator susceptibility before imposing causal support. -/
noncomputable def commutatorSusceptibility
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) (t s : ℝ) : ℂ :=
  (Complex.I / (hbar : ℂ)) *
    expectation
      ⁅heisenbergEvolution U t A,
        heisenbergEvolution U s B⁆

/-- A norm-continuous orbit of the measured observable gives a continuous scalar commutator
kernel. No boundedness assumption on the generator is needed. -/
theorem continuous_commutatorSusceptibility_timeDifference
    (expectation : NormalizedExpectation H) (A B : H →L[ℂ] H)
    (hA : Continuous (fun τ : ℝ => heisenbergEvolution U τ A)) :
    Continuous (fun τ : ℝ => commutatorSusceptibility U hbar expectation A B τ 0) := by
  have hcomm : Continuous (fun τ : ℝ =>
      heisenbergEvolution U τ A * B - B * heisenbergEvolution U τ A) :=
    (hA.mul continuous_const).sub (continuous_const.mul hA)
  have hexpect : Continuous (fun τ : ℝ => expectation
      (heisenbergEvolution U τ A * B - B * heisenbergEvolution U τ A)) :=
    expectation.toContinuousLinearMap.continuous.comp hcomm
  convert
    ((continuous_const : Continuous (fun _ : ℝ => Complex.I / (hbar : ℂ))).mul hexpect)
    using 1
  funext τ
  simp only [Pi.mul_apply, commutatorSusceptibility, heisenbergEvolution_zero,
    LieRing.of_associative_ring_bracket]

/-- Unitary Heisenberg orbits give a uniform operator-norm commutator bound. -/
theorem norm_lie_heisenbergEvolution_le (A B : H →L[ℂ] H) (t s : ℝ) :
    ‖⁅heisenbergEvolution U t A, heisenbergEvolution U s B⁆‖ ≤ 2 * ‖A‖ * ‖B‖ := by
  change ‖heisenbergEvolution U t A * heisenbergEvolution U s B -
    heisenbergEvolution U s B * heisenbergEvolution U t A‖ ≤ _
  calc
    _ ≤ ‖heisenbergEvolution U t A * heisenbergEvolution U s B‖ +
        ‖heisenbergEvolution U s B * heisenbergEvolution U t A‖ := norm_sub_le _ _
    _ ≤ ‖heisenbergEvolution U t A‖ * ‖heisenbergEvolution U s B‖ +
        ‖heisenbergEvolution U s B‖ * ‖heisenbergEvolution U t A‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖A‖ * ‖B‖ := by simp only [norm_heisenbergEvolution]; ring

/-- A unitary group gives uniform scalar commutator bounds without any continuity assumption. -/
theorem norm_commutatorSusceptibility_le
    (expectation : NormalizedExpectation H) (A B : H →L[ℂ] H) (t s : ℝ) :
    ‖commutatorSusceptibility U hbar expectation A B t s‖ ≤
      ‖Complex.I / (hbar : ℂ)‖ * ‖expectation.toContinuousLinearMap‖ *
        (2 * ‖A‖ * ‖B‖) := by
  let X : H →L[ℂ] H := ⁅heisenbergEvolution U t A, heisenbergEvolution U s B⁆
  have hX : ‖X‖ ≤ 2 * ‖A‖ * ‖B‖ := norm_lie_heisenbergEvolution_le U A B t s
  change ‖(Complex.I / (hbar : ℂ)) * expectation X‖ ≤ _
  calc
    _ = ‖Complex.I / (hbar : ℂ)‖ * ‖expectation X‖ := norm_mul _ _
    _ ≤ ‖Complex.I / (hbar : ℂ)‖ *
        (‖expectation.toContinuousLinearMap‖ * ‖X‖) :=
      mul_le_mul_of_nonneg_left (expectation.toContinuousLinearMap.le_opNorm X) (norm_nonneg _)
    _ ≤ ‖Complex.I / (hbar : ℂ)‖ *
        (‖expectation.toContinuousLinearMap‖ * (2 * ‖A‖ * ‖B‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hX (norm_nonneg _)) (norm_nonneg _)
    _ = _ := (mul_assoc _ _ _).symm

/-- The retarded susceptibility is the commutator susceptibility in the causal region and zero
when the source time lies after the observation time. -/
noncomputable def retardedSusceptibility
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) (t s : ℝ) : ℂ :=
  if s ≤ t then commutatorSusceptibility U hbar expectation A B t s else 0

@[simp]
theorem retardedSusceptibility_eq_commutatorSusceptibility_of_le
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) {t s : ℝ} (h : s ≤ t) :
    retardedSusceptibility U hbar expectation A B t s =
      commutatorSusceptibility U hbar expectation A B t s := by
  simp [retardedSusceptibility, h]

/-- The retarded susceptibility has causal support: it vanishes when `t < s`. -/
@[simp]
theorem retardedSusceptibility_eq_zero_of_lt
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) {t s : ℝ} (h : t < s) :
    retardedSusceptibility U hbar expectation A B t s = 0 := by
  simp [retardedSusceptibility, not_le.mpr h]

/-- A stationary expectation reduces the two-time commutator susceptibility to a function of the
time difference. -/
theorem commutatorSusceptibility_eq_timeDifference_of_stationary
    (expectation : NormalizedExpectation H)
    (hstationary : IsStationary U expectation)
    (A B : H →L[ℂ] H) (t s : ℝ) :
    commutatorSusceptibility U hbar expectation A B t s =
      commutatorSusceptibility U hbar expectation A B (t - s) 0 := by
  rw [commutatorSusceptibility, commutatorSusceptibility]
  simp only [heisenbergEvolution_zero]
  apply congrArg (fun z : ℂ => (Complex.I / (hbar : ℂ)) * z)
  calc
    expectation
        ⁅heisenbergEvolution U t A,
          heisenbergEvolution U s B⁆ =
      expectation
        (heisenbergEvolution U s
          ⁅heisenbergEvolution U (t - s) A, B⁆) := by
        rw [lie_heisenbergEvolution_eq_relativeTime]
    _ = expectation
        ⁅heisenbergEvolution U (t - s) A, B⁆ :=
      hstationary s ⁅heisenbergEvolution U (t - s) A, B⁆

/-- Under stationarity, the retarded kernel is the causal extension of a one-time-difference
susceptibility. -/
theorem retardedSusceptibility_eq_timeDifference_of_stationary
    (expectation : NormalizedExpectation H)
    (hstationary : IsStationary U expectation)
    (A B : H →L[ℂ] H) (t s : ℝ) :
    retardedSusceptibility U hbar expectation A B t s =
      if 0 ≤ t - s then
        commutatorSusceptibility U hbar expectation A B (t - s) 0
      else 0 := by
  by_cases h : s ≤ t
  · have hdiff : 0 ≤ t - s := sub_nonneg.mpr h
    simp [retardedSusceptibility, h, hdiff,
      commutatorSusceptibility_eq_timeDifference_of_stationary
        U hbar expectation hstationary A B t s]
  · have hdiff : ¬ 0 ≤ t - s := fun hnonneg => h (sub_nonneg.mp hnonneg)
    simp [retardedSusceptibility, h, hdiff]

/-- The scalar-source response integral is the causal convolution with the retarded
susceptibility. -/
theorem sourceCoupled_responseIntegral_eq_retardedSusceptibility
    (expectation : NormalizedExpectation H)
    (f : ℝ → ℝ) (B A : H →L[ℂ] H) {t : ℝ} (ht : 0 ≤ t) :
    ((Complex.I / (hbar : ℂ)) •
      ∫ s in (0 : ℝ)..t,
        (f s : ℂ) *
          expectation
            ⁅heisenbergEvolution U t A,
              heisenbergEvolution U s B⁆) =
      ∫ s in (0 : ℝ)..t,
        (f s : ℂ) * retardedSusceptibility U hbar expectation A B t s := by
  rw [← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) t := by
    simpa [uIcc_of_le ht] using hs
  simp [retardedSusceptibility, hs'.2, commutatorSusceptibility, smul_eq_mul]
  ring

/-- With source and times fixed, retarded susceptibility is a complex-linear functional of the
measured observable. -/
noncomputable def retardedSusceptibilityMeasuredLinearMap
    (expectation : NormalizedExpectation H)
    (source : H →L[ℂ] H) (t s : ℝ) :
    (H →L[ℂ] H) →ₗ[ℂ] ℂ where
  toFun := fun measured =>
    retardedSusceptibility U hbar expectation measured source t s
  map_add' := fun A₁ A₂ => by
    by_cases h : s ≤ t
    · simp [retardedSusceptibility, commutatorSusceptibility,
        LieRing.of_associative_ring_bracket, h, mul_add, add_mul]
      ring
    · simp [retardedSusceptibility, h]
  map_smul' := fun c A => by
    by_cases h : s ≤ t
    · simp [retardedSusceptibility, commutatorSusceptibility,
        LieRing.of_associative_ring_bracket, h, smul_eq_mul]
      ring
    · simp [retardedSusceptibility, h]

end
end LinearResponse
end QuantumTheory
