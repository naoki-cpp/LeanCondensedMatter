import Mathlib.Analysis.InnerProductSpace.l2Space

set_option linter.style.header false

/-!
# Parseval corollaries for Hilbert bases

Generic norm-square consequences of Mathlib's `HilbertBasis.hasSum_inner_mul_inner`. These lemmas
contain no operator-theory or condensed-matter content and are shared by the trace-class and
Hilbert–Schmidt developments.
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

namespace HilbertBasis

/-- **Parseval's identity for a Hilbert basis, in norm-squared form.** For any `x : H`, the
squared-magnitude Fourier coefficients of `x` against a Hilbert basis `d` sum unconditionally to
`‖x‖ ^ 2`. -/
theorem hasSum_norm_sq_inner {ι : Type*} (d : HilbertBasis ι ℂ H) (x : H) :
    HasSum (fun i => ‖(inner ℂ x (d i) : ℂ)‖ ^ 2) (‖x‖ ^ 2) := by
  have hterm :
      (fun i => ((‖(inner ℂ x (d i) : ℂ)‖ ^ 2 : ℝ) : ℂ)) =
        (fun i => inner ℂ x (d i) * inner ℂ (d i) x) := by
    funext i
    rw [show (inner ℂ (d i) x : ℂ) = starRingEnd ℂ (inner ℂ x (d i)) from
      (inner_conj_symm (d i) x).symm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hs := d.hasSum_inner_mul_inner x x
  rw [← hterm, inner_self_eq_norm_sq_to_K] at hs
  exact Complex.hasSum_ofReal.mp (by simpa using hs)

end HilbertBasis
