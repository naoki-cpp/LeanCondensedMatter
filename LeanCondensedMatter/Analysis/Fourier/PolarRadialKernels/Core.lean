import LeanCondensedMatter.Analysis.Fourier.AngularHarmonics
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Dimensionless polar Fourier kernel definitions

The phase `exp(i z cos θ)` and the zeroth, first-cosine, and second-cosine
full-angle kernels. This independent base layer provides elementary values at
the origin and continuity, without a Bessel-function representation, Fourier
momentum measure, or transport assumption.
-/

namespace QuantumTheory
namespace Transport

open AngularHarmonics

noncomputable section

open MeasureTheory
open scoped Interval ComplexConjugate

/-- Dimensionless radial phase `exp(i z cos θ)` that appears after aligning the real-space point with
the polar axis. -/
def polarFourierRadialPhase (z θ : ℝ) : ℂ :=
  Complex.exp (Complex.I * (((z * Real.cos θ : ℝ) : ℂ)))

/-- Zeroth full-angle radial Fourier kernel, identified with `2π J₀(z)` by
`polarFourierZerothAngularKernel_eq_besselJ`. -/
noncomputable def polarFourierZerothAngularKernel (z : ℝ) : ℂ :=
  ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), polarFourierRadialPhase z θ

/-- First cosine full-angle radial Fourier kernel, identified with `2π i J₁(z)`
by `polarFourierFirstCosineAngularKernel_eq_besselJ`. -/
noncomputable def polarFourierFirstCosineAngularKernel (z : ℝ) : ℂ :=
  ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
    polarFourierRadialPhase z θ * ((Real.cos θ : ℝ) : ℂ)

/-- Second cosine full-angle radial Fourier kernel, written as the `cos(2θ)`
polynomial for quadratic angular products and identified with `-2π J₂(z)`
by `polarFourierSecondCosineAngularKernel_eq_besselJ`. -/
noncomputable def polarFourierSecondCosineAngularKernel (z : ℝ) : ℂ :=
  ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
    polarFourierRadialPhase z θ *
      ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2))

/-- The Fourier phase has unit norm for every real argument. -/
theorem norm_polarFourierRadialPhase (z θ : ℝ) :
    ‖polarFourierRadialPhase z θ‖ = 1 := by
  simp [polarFourierRadialPhase, Complex.norm_exp, Complex.mul_re]

/-- Derivative of the dimensionless radial Fourier phase with respect to the polar angle. -/
theorem polarFourierRadialPhase_hasDerivAt (z θ : ℝ) :
    HasDerivAt (polarFourierRadialPhase z)
      ((-Complex.I * (z : ℂ) * ((Real.sin θ : ℝ) : ℂ)) *
        polarFourierRadialPhase z θ) θ := by
  have hcos : HasDerivAt (fun t : ℝ => ((z * Real.cos t : ℝ) : ℂ))
      ((-z * Real.sin θ : ℝ) : ℂ) θ := by
    simpa using ((Real.hasDerivAt_cos θ).const_mul z).ofReal_comp
  have harg : HasDerivAt
      (fun t : ℝ => Complex.I * ((z * Real.cos t : ℝ) : ℂ))
      (Complex.I * ((-z * Real.sin θ : ℝ) : ℂ)) θ :=
    hcos.const_mul Complex.I
  have hphase := (Complex.hasDerivAt_exp _).comp θ harg
  convert hphase using 1
  · rfl
  · simp [polarFourierRadialPhase]
    ring

/-- Derivative of the dimensionless Fourier phase with respect to its radial argument. -/
theorem polarFourierRadialPhase_hasDerivAt_radius (z θ : ℝ) :
    HasDerivAt (fun t : ℝ => polarFourierRadialPhase t θ)
      (Complex.I * ((Real.cos θ : ℝ) : ℂ) *
        polarFourierRadialPhase z θ) z := by
  have hmul : HasDerivAt (fun t : ℝ => t * Real.cos θ)
      (Real.cos θ) z := by
    simpa using (hasDerivAt_id z).mul_const (Real.cos θ)
  have harg : HasDerivAt
      (fun t : ℝ => Complex.I * ((t * Real.cos θ : ℝ) : ℂ))
      (Complex.I * ((Real.cos θ : ℝ) : ℂ)) z :=
    hmul.ofReal_comp |>.const_mul Complex.I
  have hphase := (Complex.hasDerivAt_exp _).comp z harg
  convert hphase using 1
  · rfl
  · dsimp [polarFourierRadialPhase]
    ring

/-- Complex conjugation of the angular Fourier phase reverses its radial argument. -/
theorem polarFourierRadialPhase_conj (z θ : ℝ) :
    conj (polarFourierRadialPhase z θ) =
      polarFourierRadialPhase (-z) θ := by
  unfold polarFourierRadialPhase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- The zeroth radial Fourier kernel is normalized by the full polar angle at the origin. -/
@[simp] theorem polarFourierZerothAngularKernel_zero :
    polarFourierZerothAngularKernel 0 = ((2 * Real.pi : ℝ) : ℂ) := by
  simp [polarFourierZerothAngularKernel, polarFourierRadialPhase]

/-- The zeroth full-angle Fourier phase has vanishing first cosine harmonic. -/
@[simp] theorem polarFourierFirstCosineAngularKernel_zero :
    polarFourierFirstCosineAngularKernel 0 = 0 := by
  simpa [polarFourierFirstCosineAngularKernel, polarFourierRadialPhase] using
    (integral_cos_mul_complex (z := (1 : ℂ)) one_ne_zero (0 : ℝ) (2 * Real.pi))

/-- The second-cosine angular Fourier kernel vanishes at zero radial argument. -/
@[simp] theorem polarFourierSecondCosineAngularKernel_zero :
    polarFourierSecondCosineAngularKernel 0 = 0 := by
  let coefficients : AngularHarmonicCoefficients ℂ :=
    { constant := 0
      firstCosine := 0
      firstSine := 0
      secondCosine := 1
      secondMixed := 0 }
  simpa [coefficients, AngularHarmonicCoefficients.eval,
    polarFourierSecondCosineAngularKernel, polarFourierRadialPhase,
    smul_eq_mul] using coefficients.integral_eval

@[fun_prop]
theorem continuous_polarFourierZerothAngularKernel :
    Continuous polarFourierZerothAngularKernel := by
  unfold polarFourierZerothAngularKernel
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  unfold Function.uncurry polarFourierRadialPhase
  fun_prop

@[fun_prop]
theorem continuous_polarFourierFirstCosineAngularKernel :
    Continuous polarFourierFirstCosineAngularKernel := by
  unfold polarFourierFirstCosineAngularKernel
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  unfold Function.uncurry polarFourierRadialPhase
  fun_prop

@[fun_prop]
theorem continuous_polarFourierSecondCosineAngularKernel :
    Continuous polarFourierSecondCosineAngularKernel := by
  unfold polarFourierSecondCosineAngularKernel
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  unfold Function.uncurry polarFourierRadialPhase
  fun_prop


end
end Transport
end QuantumTheory
