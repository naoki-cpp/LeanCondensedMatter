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

end

end QuantumTheory.Transport
