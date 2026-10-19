import LeanCondensedMatter.QuantumTheory.LinearResponse.Dynamics.Stationarity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Lie.OfAssociative

set_option linter.style.header false

/-!
# Retarded susceptibility for bounded linear response

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
-/

namespace QuantumTheory
namespace LinearResponse

attribute [local instance 100] LieRing.ofAssociativeRing

open Set

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (system : BoundedFreeSystem H)

/-- The two-time commutator susceptibility before imposing causal support. -/
noncomputable def commutatorSusceptibility
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) (t s : ℝ) : ℂ :=
  (Complex.I / (system.hbar : ℂ)) *
    expectation
      ⁅heisenbergEvolution system t A, heisenbergEvolution system s B⁆

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
  calc
    expectation
        ⁅heisenbergEvolution system t A, heisenbergEvolution system s B⁆ =
      expectation
        (heisenbergEvolution system s ⁅heisenbergEvolution system (t - s) A, B⁆) := by
        rw [lie_heisenbergEvolution_eq_relativeTime]
    _ = expectation
        ⁅heisenbergEvolution system (t - s) A, B⁆ :=
      hstationary s ⁅heisenbergEvolution system (t - s) A, B⁆

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
            ⁅heisenbergEvolution system t A, heisenbergEvolution system s B⁆) =
      ∫ s in (0 : ℝ)..t,
        (f s : ℂ) * retardedSusceptibility system expectation A B t s := by
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
    retardedSusceptibility system expectation measured source t s
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
