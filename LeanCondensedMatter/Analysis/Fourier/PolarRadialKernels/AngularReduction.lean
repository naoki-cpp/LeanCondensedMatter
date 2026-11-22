import LeanCondensedMatter.Analysis.Fourier.PolarRadialKernels.Core
import LeanCondensedMatter.Analysis.Fourier.AngularHarmonics
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Polar Fourier angular harmonic reductions

Reduction of constant, first and second angular harmonics against the
radial Fourier phase, together with reflection cancellations and arbitrary
polar-angle shifts. This layer depends only on the core kernels and
model-independent harmonic coefficients.
-/

namespace QuantumTheory
open AngularHarmonics
namespace Transport

noncomputable section

open MeasureTheory
open scoped Interval ComplexConjugate

/-- Reflection across π makes the full-period integral of an antisymmetric
complex-valued integrand vanish. -/
private theorem integral_fullPeriod_eq_zero_of_reflection_neg
    (f : ℝ → ℂ) (hneg : ∀ θ, f (2 * Real.pi - θ) = -f θ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ) = 0 := by
  have hsub :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f (2 * Real.pi - θ)) =
        ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ := by
    simpa using
      (intervalIntegral.integral_comp_sub_left
        (f := f) (a := (0 : ℝ)) (b := 2 * Real.pi) (2 * Real.pi))
  have hflip :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f (2 * Real.pi - θ)) =
        -(∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ) := by
    simp_rw [hneg, intervalIntegral.integral_neg]
  exact CharZero.neg_eq_self_iff.mp (hflip.symm.trans hsub)

/-- The sine first harmonic vanishes against the radial Fourier phase over one full angle. -/
theorem integral_polarFourierRadialPhase_mul_sin_zero (z : ℝ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      polarFourierRadialPhase z θ * ((Real.sin θ : ℝ) : ℂ)) = 0 := by
  apply integral_fullPeriod_eq_zero_of_reflection_neg
  intro θ
  unfold polarFourierRadialPhase
  rw [Real.cos_two_pi_sub, Real.sin_two_pi_sub]
  push_cast
  ring

/-- The mixed quadratic harmonic `cos θ sin θ` vanishes against the radial Fourier phase over one
full angle. -/
theorem integral_polarFourierRadialPhase_mul_cos_mul_sin_zero (z : ℝ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      polarFourierRadialPhase z θ *
        (((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ))) = 0 := by
  apply integral_fullPeriod_eq_zero_of_reflection_neg
  intro θ
  unfold polarFourierRadialPhase
  rw [Real.cos_two_pi_sub, Real.sin_two_pi_sub]
  push_cast
  ring

/-- Phase-weighted full-angle integration of the canonical constant/first/second harmonic
decomposition. The first-sine and mixed-second channels vanish on the radial axis. -/
theorem integral_polarFourierRadialPhase_harmonicCoefficients
    (coefficients : AngularHarmonicCoefficients ℂ) (z p : ℝ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      ((p : ℂ) * polarFourierRadialPhase z θ) * coefficients.eval θ) =
      (p : ℂ) *
        (polarFourierZerothAngularKernel z * coefficients.constant +
          polarFourierFirstCosineAngularKernel z * coefficients.firstCosine +
          polarFourierSecondCosineAngularKernel z * coefficients.secondCosine) := by
  calc
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
        ((p : ℂ) * polarFourierRadialPhase z θ) * coefficients.eval θ) =
        (p : ℂ) * ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
          polarFourierRadialPhase z θ * coefficients.eval θ := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro θ _
      ring
    _ = _ := by
      congr 1
      simp only [AngularHarmonicCoefficients.eval, smul_eq_mul]
      simp_rw [mul_add, ← mul_assoc]
      repeat' rw [intervalIntegral.integral_add
        (by apply Continuous.intervalIntegrable; unfold polarFourierRadialPhase; fun_prop)
        (by apply Continuous.intervalIntegrable; unfold polarFourierRadialPhase; fun_prop)]
      simp only [intervalIntegral.integral_mul_const]
      simp_rw [mul_assoc]
      simp only [integral_polarFourierRadialPhase_mul_sin_zero,
        integral_polarFourierRadialPhase_mul_cos_mul_sin_zero]
      simp [polarFourierZerothAngularKernel, polarFourierFirstCosineAngularKernel,
        polarFourierSecondCosineAngularKernel]

/-- Full-angle reduction for a scalar field containing only constant and first sine/cosine
harmonics. The sine harmonic drops out on the radial axis, leaving the zeroth and first-cosine
kernels that later become the `J₀` and `J₁` channels. -/
theorem integral_polarFourierRadialPhase_first_harmonics
    (z p : ℝ) (a b c : ℂ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      ((p : ℂ) * polarFourierRadialPhase z θ) *
        (a + ((Real.cos θ : ℝ) : ℂ) * b + ((Real.sin θ : ℝ) : ℂ) * c)) =
      (p : ℂ) *
        (polarFourierZerothAngularKernel z * a +
          polarFourierFirstCosineAngularKernel z * b) := by
  let coefficients : AngularHarmonicCoefficients ℂ :=
    { constant := a
      firstCosine := b
      firstSine := c
      secondCosine := 0
      secondMixed := 0 }
  simpa [coefficients, AngularHarmonicCoefficients.eval, smul_eq_mul] using
    integral_polarFourierRadialPhase_harmonicCoefficients coefficients z p

private theorem integral_polarFourierRadialPhase_shifted_second_harmonics
    (z p angle : ℝ) (a b c d e : ℂ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      ((p : ℂ) * polarFourierRadialPhase z (θ - angle)) *
        (a + ((Real.cos θ : ℝ) : ℂ) * b + ((Real.sin θ : ℝ) : ℂ) * c +
          ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2)) * d +
          (((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ)) * e)) =
      (p : ℂ) *
        (polarFourierZerothAngularKernel z * a +
          polarFourierFirstCosineAngularKernel z *
            (((Real.cos angle : ℝ) : ℂ) * b + ((Real.sin angle : ℝ) : ℂ) * c) +
          polarFourierSecondCosineAngularKernel z *
            (((((Real.cos angle : ℝ) : ℂ) ^ 2) -
                (((Real.sin angle : ℝ) : ℂ) ^ 2)) * d +
              (((Real.cos angle : ℝ) : ℂ) * ((Real.sin angle : ℝ) : ℂ)) * e)) := by
  let f : ℝ → ℂ := fun α =>
    ((p : ℂ) * polarFourierRadialPhase z α) *
      (a + ((Real.cos (α + angle) : ℝ) : ℂ) * b +
        ((Real.sin (α + angle) : ℝ) : ℂ) * c +
        ((((Real.cos (α + angle) : ℝ) : ℂ) ^ 2) -
          (((Real.sin (α + angle) : ℝ) : ℂ) ^ 2)) * d +
        (((Real.cos (α + angle) : ℝ) : ℂ) *
          ((Real.sin (α + angle) : ℝ) : ℂ)) * e)
  have hf : Function.Periodic f (2 * Real.pi) := by
    intro α
    simp only [f, polarFourierRadialPhase]
    rw [Real.cos_add_two_pi]
    have hangle : α + 2 * Real.pi + angle = (α + angle) + 2 * Real.pi := by
      ring
    rw [hangle, Real.cos_add_two_pi, Real.sin_add_two_pi]
  calc
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
        ((p : ℂ) * polarFourierRadialPhase z (θ - angle)) *
          (a + ((Real.cos θ : ℝ) : ℂ) * b + ((Real.sin θ : ℝ) : ℂ) * c +
            ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2)) * d +
            (((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ)) * e)) =
        ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f (θ - angle) := by
          apply intervalIntegral.integral_congr
          intro θ _
          simp [f]
    _ = ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ := by
      rw [intervalIntegral.integral_comp_sub_right]
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        hf.intervalIntegral_add_eq (-angle) 0
    _ = (p : ℂ) *
        (polarFourierZerothAngularKernel z * a +
          polarFourierFirstCosineAngularKernel z *
            (((Real.cos angle : ℝ) : ℂ) * b + ((Real.sin angle : ℝ) : ℂ) * c) +
          polarFourierSecondCosineAngularKernel z *
            (((((Real.cos angle : ℝ) : ℂ) ^ 2) -
                (((Real.sin angle : ℝ) : ℂ) ^ 2)) * d +
              (((Real.cos angle : ℝ) : ℂ) * ((Real.sin angle : ℝ) : ℂ)) * e)) := by
      let coefficients : AngularHarmonicCoefficients ℂ :=
        { constant := a
          firstCosine :=
            ((Real.cos angle : ℝ) : ℂ) * b + ((Real.sin angle : ℝ) : ℂ) * c
          firstSine :=
            -((Real.sin angle : ℝ) : ℂ) * b + ((Real.cos angle : ℝ) : ℂ) * c
          secondCosine :=
            (((Real.cos angle : ℝ) : ℂ) ^ 2 - ((Real.sin angle : ℝ) : ℂ) ^ 2) * d +
              ((Real.cos angle : ℝ) : ℂ) * ((Real.sin angle : ℝ) : ℂ) * e
          secondMixed :=
            -4 * (((Real.cos angle : ℝ) : ℂ) * ((Real.sin angle : ℝ) : ℂ)) * d +
              (((Real.cos angle : ℝ) : ℂ) ^ 2 - ((Real.sin angle : ℝ) : ℂ) ^ 2) * e }
      have hchange :
          (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ) =
            ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
              ((p : ℂ) * polarFourierRadialPhase z θ) * coefficients.eval θ := by
        apply intervalIntegral.integral_congr
        intro θ _
        simp only [f, coefficients, AngularHarmonicCoefficients.eval, smul_eq_mul]
        rw [Real.cos_add, Real.sin_add]
        push_cast
        ring
      rw [hchange]
      simpa [coefficients, AngularHarmonicCoefficients.eval, smul_eq_mul] using
        integral_polarFourierRadialPhase_harmonicCoefficients coefficients z p

/-- Phase-weighted full-angle reduction of canonical harmonic coefficients at an arbitrary
real-space polar angle. -/
theorem integral_polarFourierRadialPhase_harmonicCoefficients_shifted
    (coefficients : AngularHarmonicCoefficients ℂ) (z p angle : ℝ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      ((p : ℂ) * polarFourierRadialPhase z (θ - angle)) * coefficients.eval θ) =
      (p : ℂ) *
        (polarFourierZerothAngularKernel z * coefficients.constant +
          polarFourierFirstCosineAngularKernel z *
            (((Real.cos angle : ℝ) : ℂ) * coefficients.firstCosine +
              ((Real.sin angle : ℝ) : ℂ) * coefficients.firstSine) +
          polarFourierSecondCosineAngularKernel z *
            (((((Real.cos angle : ℝ) : ℂ) ^ 2) -
                (((Real.sin angle : ℝ) : ℂ) ^ 2)) * coefficients.secondCosine +
              (((Real.cos angle : ℝ) : ℂ) * ((Real.sin angle : ℝ) : ℂ)) *
                coefficients.secondMixed)) := by
  simpa [AngularHarmonicCoefficients.eval, smul_eq_mul] using
    (integral_polarFourierRadialPhase_shifted_second_harmonics
      z p angle coefficients.constant coefficients.firstCosine coefficients.firstSine
      coefficients.secondCosine coefficients.secondMixed)

end
end Transport
end QuantumTheory
