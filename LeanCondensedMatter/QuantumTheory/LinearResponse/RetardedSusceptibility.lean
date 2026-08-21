import LeanCondensedMatter.QuantumTheory.LinearResponse.SourceCoupling

set_option linter.style.header false

/-!
# Retarded susceptibility for bounded linear response

This module names the two-time commutator kernel underlying the source-coupled Kubo formula and
extends it by zero outside the causal region `s ≤ t`.

For an ordinary normalized expectation `ω`,

`χ_AB(t,s) = (i / ℏ) ω(A_I(t) B_I(s) - B_I(s) A_I(t))`

and

`χᴿ_AB(t,s) = if s ≤ t then χ_AB(t,s) else 0`.

The source response is the causal convolution `∫₀ᵗ f(s) χᴿ_AB(t,s) ds`. Under stationarity, the
two-time kernel is reduced to a function of the time difference without adding a separate
correlation-function invariance axiom.
-/

namespace QuantumTheory
namespace LinearResponse

open Set

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (system : BoundedFreeSystem H)

/-- Applying free Heisenberg evolution successively adds the two time parameters. -/
@[simp]
theorem heisenbergEvolution_heisenbergEvolution
    (A : H →L[ℂ] H) (t s : ℝ) :
    heisenbergEvolution system (heisenbergEvolution system A t) s =
      heisenbergEvolution system A (t + s) := by
  change
    freePropagator system (-s) *
        (freePropagator system (-t) * A * freePropagator system t) *
        freePropagator system s =
      freePropagator system (-(t + s)) * A * freePropagator system (t + s)
  rw [show -(t + s) = -s + -t by ring, freePropagator_add, freePropagator_add]
  noncomm_ring

/-- Free Heisenberg evolution preserves operator multiplication. -/
@[simp]
theorem heisenbergEvolution_mul
    (A B : H →L[ℂ] H) (t : ℝ) :
    heisenbergEvolution system (A * B) t =
      heisenbergEvolution system A t * heisenbergEvolution system B t := by
  change
    freePropagator system (-t) * (A * B) * freePropagator system t =
      (freePropagator system (-t) * A * freePropagator system t) *
        (freePropagator system (-t) * B * freePropagator system t)
  calc
    _ = freePropagator system (-t) * A * 1 * B * freePropagator system t := by
      noncomm_ring
    _ = freePropagator system (-t) * A *
        (freePropagator system t * freePropagator system (-t)) * B *
          freePropagator system t := by
      rw [freePropagator_mul_neg]
    _ = _ := by
      noncomm_ring

/-- Free Heisenberg evolution preserves operator subtraction. -/
@[simp]
theorem heisenbergEvolution_sub
    (A B : H →L[ℂ] H) (t : ℝ) :
    heisenbergEvolution system (A - B) t =
      heisenbergEvolution system A t - heisenbergEvolution system B t := by
  simp [heisenbergEvolution, mul_sub, sub_mul]

/-- The two-time commutator susceptibility before imposing causal support. -/
noncomputable def commutatorSusceptibility
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) (t s : ℝ) : ℂ :=
  (Complex.I / (system.hbar : ℂ)) *
    expectation
      (heisenbergEvolution system A t * heisenbergEvolution system B s -
        heisenbergEvolution system B s * heisenbergEvolution system A t)

/-- The retarded susceptibility is the commutator susceptibility in the causal region and zero
when the source time lies after the observation time. -/
noncomputable def retardedSusceptibility
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) (t s : ℝ) : ℂ :=
  if s ≤ t then commutatorSusceptibility system expectation A B t s else 0

@[simp]
theorem retardedSusceptibility_eq_commutatorSusceptibility_of_le
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) {t s : ℝ} (h : s ≤ t) :
    retardedSusceptibility system expectation A B t s =
      commutatorSusceptibility system expectation A B t s := by
  simp [retardedSusceptibility, h]

/-- The retarded susceptibility has causal support: it vanishes when `t < s`. -/
@[simp]
theorem retardedSusceptibility_eq_zero_of_lt
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) {t s : ℝ} (h : t < s) :
    retardedSusceptibility system expectation A B t s = 0 := by
  simp [retardedSusceptibility, not_le.mpr h]

/-- A stationary expectation reduces the two-time commutator susceptibility to a function of the
time difference. -/
theorem commutatorSusceptibility_eq_timeDifference_of_stationary
    (expectation : NormalizedExpectation H)
    (hstationary : IsStationary system expectation)
    (A B : H →L[ℂ] H) (t s : ℝ) :
    commutatorSusceptibility system expectation A B t s =
      commutatorSusceptibility system expectation A B (t - s) 0 := by
  rw [commutatorSusceptibility, commutatorSusceptibility]
  simp only [heisenbergEvolution_zero]
  apply congrArg (fun z : ℂ => (Complex.I / (system.hbar : ℂ)) * z)
  let C : H →L[ℂ] H :=
    heisenbergEvolution system A (t - s) * B -
      B * heisenbergEvolution system A (t - s)
  have hA :
      heisenbergEvolution system (heisenbergEvolution system A (t - s)) s =
        heisenbergEvolution system A t := by
    rw [heisenbergEvolution_heisenbergEvolution]
    congr 1
    ring
  calc
    expectation
        (heisenbergEvolution system A t * heisenbergEvolution system B s -
          heisenbergEvolution system B s * heisenbergEvolution system A t) =
      expectation (heisenbergEvolution system C s) := by
        congr 1
        simp [C, hA]
    _ = expectation C := hstationary s C
    _ = expectation
        (heisenbergEvolution system A (t - s) * B -
          B * heisenbergEvolution system A (t - s)) := by
        rfl

/-- Under stationarity, the retarded kernel is the causal extension of a one-time-difference
susceptibility. -/
theorem retardedSusceptibility_eq_timeDifference_of_stationary
    (expectation : NormalizedExpectation H)
    (hstationary : IsStationary system expectation)
    (A B : H →L[ℂ] H) (t s : ℝ) :
    retardedSusceptibility system expectation A B t s =
      if 0 ≤ t - s then
        commutatorSusceptibility system expectation A B (t - s) 0
      else 0 := by
  by_cases h : s ≤ t
  · have hdiff : 0 ≤ t - s := sub_nonneg.mpr h
    simp [retardedSusceptibility, h, hdiff,
      commutatorSusceptibility_eq_timeDifference_of_stationary
        system expectation hstationary A B t s]
  · have hdiff : ¬ 0 ≤ t - s := fun hnonneg => h (sub_nonneg.mp hnonneg)
    simp [retardedSusceptibility, h, hdiff]

/-- The scalar-source response integral is the causal convolution with the retarded
susceptibility. -/
theorem sourceCoupled_responseIntegral_eq_retardedSusceptibility
    (expectation : NormalizedExpectation H)
    (f : ℝ → ℝ) (B A : H →L[ℂ] H) {t : ℝ} (ht : 0 ≤ t) :
    ((Complex.I / (system.hbar : ℂ)) •
      ∫ s in (0 : ℝ)..t,
        (f s : ℂ) *
          expectation
            (heisenbergEvolution system A t * heisenbergEvolution system B s -
              heisenbergEvolution system B s * heisenbergEvolution system A t)) =
      ∫ s in (0 : ℝ)..t,
        (f s : ℂ) * retardedSusceptibility system expectation A B t s := by
  rw [← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) t := by
    simpa [uIcc_of_le ht] using hs
  simp [retardedSusceptibility, hs'.2, commutatorSusceptibility, smul_eq_mul]
  ring

/-- The bounded scalar-source Kubo formula written as a causal convolution with the retarded
susceptibility. -/
theorem hasDerivAt_sourceCoupledPerturbedExpectation_zero_of_bound_retarded
    (expectation : NormalizedExpectation H)
    (f : ℝ → ℝ) {B : H →L[ℂ] H} (hB : IsSelfAdjoint B)
    (A : H →L[ℂ] H) {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Icc (0 : ℝ) β,
      ‖timeDependentInteractionPerturbation system
        (sourceCoupledPerturbation f B) s‖ ≤ M)
    (ht : t ∈ Icc (0 : ℝ) β)
    (hInt : IntervalIntegrable
      (timeDependentInteractionPerturbation system
        (sourceCoupledPerturbation f B)) MeasureTheory.volume 0 t) :
    HasDerivAt
      (fun lam : ℝ =>
        timeDependentPerturbedExpectationFunctional system expectation
          (sourceCoupledPerturbation f B) lam t A)
      (∫ s in (0 : ℝ)..t,
        (f s : ℂ) * retardedSusceptibility system expectation A B t s)
      0 := by
  have h := hasDerivAt_sourceCoupledPerturbedExpectation_zero_of_bound_kubo
    system expectation f hB A hM hV ht hInt
  rw [sourceCoupled_responseIntegral_eq_retardedSusceptibility
    system expectation f B A ht.1] at h
  exact h

end
end LinearResponse
end QuantumTheory
