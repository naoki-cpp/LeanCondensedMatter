import LeanCondensedMatter.Analysis.Fourier.AngularHarmonics
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FunProp

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
open scoped Interval

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

/-- The zeroth full-angle Fourier phase has vanishing first cosine harmonic. -/
@[simp] theorem polarFourierFirstCosineAngularKernel_zero :
    polarFourierFirstCosineAngularKernel 0 = 0 := by
  have h := integral_cos_mul_complex (z := (1 : ℂ)) one_ne_zero (0 : ℝ) (2 * Real.pi)
  simpa [polarFourierFirstCosineAngularKernel, polarFourierRadialPhase] using h
/-- Second cosine full-angle radial Fourier kernel, written as the `cos(2θ)`
polynomial for quadratic angular products and identified with `-2π J₂(z)`
by `polarFourierSecondCosineAngularKernel_eq_besselJ`. -/
noncomputable def polarFourierSecondCosineAngularKernel (z : ℝ) : ℂ :=
  ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
    polarFourierRadialPhase z θ *
      ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2))

/-- The zeroth radial Fourier kernel is normalized by the full polar angle at the origin. -/
@[simp] theorem polarFourierZerothAngularKernel_zero :
    polarFourierZerothAngularKernel 0 = ((2 * Real.pi : ℝ) : ℂ) := by
  simp [polarFourierZerothAngularKernel, polarFourierRadialPhase]

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

/-- The second-cosine angular Fourier kernel vanishes at zero radial argument. -/
@[simp] theorem polarFourierSecondCosineAngularKernel_zero :
    polarFourierSecondCosineAngularKernel 0 = 0 := by
  let coefficients : AngularHarmonicCoefficients ℂ :=
    { constant := 0
      firstCosine := 0
      firstSine := 0
      secondCosine := 1
      secondMixed := 0 }
  have h := coefficients.integral_eval
  simpa [coefficients, AngularHarmonicCoefficients.eval,
    polarFourierSecondCosineAngularKernel, polarFourierRadialPhase,
    smul_eq_mul] using h

end
end Transport
end QuantumTheory
