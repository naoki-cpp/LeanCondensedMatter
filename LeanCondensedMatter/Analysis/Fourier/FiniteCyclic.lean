import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option linter.style.header false

/-!
# Normalized Fourier modes on a finite cyclic group

The positive-exponent convention uses the standard additive character of `ZMod N`.
The inner product is the counting-measure inner product of `EuclideanSpace`.
-/

namespace ZMod

open scoped BigOperators InnerProductSpace

noncomputable section
variable {N : ℕ} [NeZero N]

/-- The normalized positive-exponent Fourier mode on a finite cyclic group. -/
def fourierMode (q : ZMod N) : EuclideanSpace ℂ (ZMod N) :=
  WithLp.toLp 2 fun j => (Real.sqrt N : ℂ)⁻¹ * stdAddChar (q * j)

theorem stdAddChar_conj (j : ZMod N) :
    conj (stdAddChar j) = stdAddChar (-j) := by
  rw [stdAddChar_apply, stdAddChar_apply, AddChar.map_neg_eq_inv,
    Circle.coe_inv_eq_conj]

private theorem sum_stdAddChar_mul (q : ZMod N) :
    ∑ j : ZMod N, stdAddChar (q * j) = if q = 0 then (N : ℂ) else 0 := by
  split_ifs with h
  · simp [h, ZMod.card]
  · exact AddChar.sum_eq_zero_of_ne_one (isPrimitive_stdAddChar N h)

theorem orthonormal_fourierMode : Orthonormal ℂ (fourierMode (N := N)) := by
  rw [orthonormal_iff_ite]
  intro q r
  have hN : (N : ℝ) > 0 := by exact_mod_cast NeZero.pos N
  have hs : (Real.sqrt N : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hN).ne'
  have hsq : (Real.sqrt N : ℂ) ^ 2 = N := by
    exact_mod_cast Real.sq_sqrt hN.le
  have hterm (j : ZMod N) :
      inner ℂ (fourierMode q j) (fourierMode r j) =
        ((Real.sqrt N : ℂ)⁻¹) ^ 2 * stdAddChar ((r - q) * j) := by
    simp only [fourierMode, PiLp.toLp_apply, RCLike.inner_apply, map_mul,
      map_inv₀, Complex.conj_ofReal, stdAddChar_conj, sub_mul,
      AddChar.map_add_eq_mul, sub_eq_add_neg, neg_mul]
    ring
  rw [PiLp.inner_apply]
  simp_rw [hterm]
  rw [← Finset.mul_sum, sum_stdAddChar_mul]
  by_cases h : q = r
  · subst r
    simp only [sub_self, ite_true, mul_one]
    field_simp
    exact hsq.symm
  · simp [sub_eq_zero, Ne.symm h, h]

/-- The normalized Fourier modes as a complete orthonormal basis. -/
def fourierBasis : OrthonormalBasis (ZMod N) ℂ (EuclideanSpace ℂ (ZMod N)) :=
  (basisOfOrthonormalOfCardEqFinrank orthonormal_fourierMode
    (by simp)).toOrthonormalBasis (by
      simpa using (orthonormal_fourierMode (N := N)))

theorem fourierBasis_apply (q : ZMod N) : fourierBasis q = fourierMode q := by
  simp [fourierBasis]

end
end ZMod
