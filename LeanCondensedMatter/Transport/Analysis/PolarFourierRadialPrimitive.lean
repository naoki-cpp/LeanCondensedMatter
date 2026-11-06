import LeanCondensedMatter.Transport.Analysis.PolarFourierRadialDerivative
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# First-harmonic primitive for the radial Fourier transform

The exact first-harmonic recurrence and derivative identities imply
`(z K₁(z))' = i z K₀(z)`. Its scaled version is the integration-by-parts
identity needed to control the ultraviolet tail of a radial Green kernel
without introducing an unproved Bessel Y/Hankel branch.
-/

namespace QuantumTheory.Transport

noncomputable section

/-- The first Fourier harmonic is a primitive of the radial zeroth
harmonic: `(z K₁(z))' = i z K₀(z)` for all real `z`. -/
theorem polarFourierFirstCosineAngularKernel_mul_argument_hasDerivAt
    (z : ℝ) :
    HasDerivAt (fun t : ℝ =>
      (t : ℂ) * polarFourierFirstCosineAngularKernel t)
      (Complex.I * (z : ℂ) * polarFourierZerothAngularKernel z) z := by
  have h := ((hasDerivAt_id z).ofReal_comp).mul
    (polarFourierFirstCosineAngularKernel_hasDerivAt z)
  have hrec :=
    polarFourierFirstCosineAngularKernel_two_mul_eq_zeroth_sub_second z
  have hcoef :
      polarFourierFirstCosineAngularKernel z +
        (z : ℂ) * ((Complex.I / 2) *
          (polarFourierZerothAngularKernel z +
            polarFourierSecondCosineAngularKernel z)) =
        Complex.I * (z : ℂ) * polarFourierZerothAngularKernel z := by
    calc
      _ = Complex.I * (z : ℂ) * polarFourierZerothAngularKernel z +
          (1 / 2 : ℂ) *
            (2 * polarFourierFirstCosineAngularKernel z -
              Complex.I * (z : ℂ) *
                (polarFourierZerothAngularKernel z -
                  polarFourierSecondCosineAngularKernel z)) := by ring
      _ = _ := by rw [hrec]; ring
  convert h using 1
  · rfl
  · exact hcoef.symm

/-- The scaled radial primitive. The Fourier scale `c` may have either
sign, and the formula remains valid for `c = 0`. -/
theorem polarFourierFirstCosineAngularKernel_radialPrimitive_hasDerivAt
    (c p : ℝ) :
    HasDerivAt (fun x : ℝ =>
      (x : ℂ) * polarFourierFirstCosineAngularKernel (x * c))
      (Complex.I * (c : ℂ) * (p : ℂ) *
        polarFourierZerothAngularKernel (p * c)) p := by
  have harg : HasDerivAt (fun x : ℝ => x * c) c p := by
    simpa using (hasDerivAt_id p).mul_const c
  have h := ((hasDerivAt_id p).ofReal_comp).mul
    ((polarFourierFirstCosineAngularKernel_hasDerivAt (p * c)).comp p harg)
  have hrec :=
    polarFourierFirstCosineAngularKernel_two_mul_eq_zeroth_sub_second (p * c)
  have hcoef :
      polarFourierFirstCosineAngularKernel (p * c) +
        (p : ℂ) *
          (((Complex.I / 2) *
            (polarFourierZerothAngularKernel (p * c) +
              polarFourierSecondCosineAngularKernel (p * c))) * (c : ℂ)) =
        Complex.I * (c : ℂ) * (p : ℂ) *
          polarFourierZerothAngularKernel (p * c) := by
    have hrec' :
        2 * polarFourierFirstCosineAngularKernel (p * c) =
          Complex.I * ((p : ℂ) * (c : ℂ)) *
            (polarFourierZerothAngularKernel (p * c) -
              polarFourierSecondCosineAngularKernel (p * c)) := by
      simpa only [Complex.ofReal_mul] using hrec
    calc
      _ = Complex.I * (c : ℂ) * (p : ℂ) *
            polarFourierZerothAngularKernel (p * c) +
          (1 / 2 : ℂ) *
            (2 * polarFourierFirstCosineAngularKernel (p * c) -
              Complex.I * ((p : ℂ) * (c : ℂ)) *
                (polarFourierZerothAngularKernel (p * c) -
                  polarFourierSecondCosineAngularKernel (p * c))) := by ring
      _ = _ := by rw [hrec']; ring
  convert h using 1
  · rfl
  · exact hcoef.symm

/-- Integration by parts for a finite radial Fourier transform, with no
restriction on the (possibly zero or negative) Fourier scale `c`.
The first harmonic replaces the zeroth one at the cost of differentiating
the radial weight. This is the exact finite-cutoff identity used before
taking the ultraviolet limit of a massive-Dirac Green integral. -/
theorem integral_polarFourierZerothAngularKernel_mul_weight_by_parts
    (c a b : ℝ) (weight weight' : ℝ → ℂ)
    (hweight : ∀ p : ℝ, HasDerivAt weight (weight' p) p)
    (hweight' : Continuous weight') :
    (Complex.I * (c : ℂ)) *
        (∫ p in a..b, (p : ℂ) *
          polarFourierZerothAngularKernel (p * c) * weight p) =
      ((b : ℂ) * polarFourierFirstCosineAngularKernel (b * c) * weight b) -
      ((a : ℂ) * polarFourierFirstCosineAngularKernel (a * c) * weight a) -
      (∫ p in a..b,
        (p : ℂ) * polarFourierFirstCosineAngularKernel (p * c) * weight' p) := by
  let u : ℝ → ℂ := fun p =>
    (p : ℂ) * polarFourierFirstCosineAngularKernel (p * c)
  let u' : ℝ → ℂ := fun p =>
    Complex.I * (c : ℂ) * (p : ℂ) *
      polarFourierZerothAngularKernel (p * c)
  have hc0 : Continuous (fun p : ℝ => polarFourierZerothAngularKernel (p * c)) :=
    continuous_polarFourierZerothAngularKernel.comp
      (continuous_id.mul continuous_const)
  have hc1 : Continuous (fun p : ℝ => polarFourierFirstCosineAngularKernel (p * c)) :=
    continuous_polarFourierFirstCosineAngularKernel.comp
      (continuous_id.mul continuous_const)
  have hcu : Continuous u :=
    (Complex.continuous_ofReal.comp continuous_id).mul hc1
  have hcu' : Continuous u' :=
    (continuous_const.mul
      (Complex.continuous_ofReal.comp continuous_id)).mul hc0
  have hcw : Continuous weight :=
    continuous_iff_continuousAt.mpr fun p => (hweight p).continuousAt
  have hfirst : IntervalIntegrable
      (fun p : ℝ => u' p * weight p) MeasureTheory.volume a b :=
    (hcu'.mul hcw).intervalIntegrable a b
  have hsecond : IntervalIntegrable
      (fun p : ℝ => u p * weight' p) MeasureTheory.volume a b :=
    (hcu.mul hweight').intervalIntegrable a b
  have hmain := intervalIntegral.integral_deriv_mul_eq_sub
    (a := a) (b := b) (u := u) (v := weight)
    (u' := u') (v' := weight')
    (fun p _ => polarFourierFirstCosineAngularKernel_radialPrimitive_hasDerivAt c p)
    (fun p _ => hweight p)
    hfirst hsecond
  have hsum :
      (∫ p in a..b, u' p * weight p) +
        (∫ p in a..b, u p * weight' p) =
          u b * weight b - u a * weight a := by
    rw [← intervalIntegral.integral_add hfirst hsecond]
    exact hmain
  calc
    _ = ∫ p in a..b, u' p * weight p := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro p _
      dsimp [u']
      ring
    _ = (u b * weight b - u a * weight a) -
          (∫ p in a..b, u p * weight' p) :=
      eq_sub_iff_add_eq.mpr hsum
    _ = _ := rfl

end

end QuantumTheory.Transport
