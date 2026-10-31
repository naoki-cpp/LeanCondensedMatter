import LeanCondensedMatter.Analysis.Fourier.FiniteCyclic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option linter.style.header false

/-!
# Weighted Laplacian on a finite cyclic group

The operator is w times the nearest-neighbor difference 2f(i) - f(i-1) - f(i+1).
Its normalized positive-exponent Fourier eigenbasis is the canonical cyclic basis.
The weight is real; no spin representation or physical energy convention is assumed.
-/

namespace ZMod

open scoped BigOperators InnerProductSpace

noncomputable section
variable {N : ℕ} [NeZero N]

/-- The real-weighted nearest-neighbor Laplacian on a finite cyclic group. -/
def cyclicLaplacian (w : ℝ) : EuclideanSpace ℂ (ZMod N) →ₗ[ℂ]
    EuclideanSpace ℂ (ZMod N) where
  toFun ψ := WithLp.toLp 2 fun i => (w : ℂ) * (2 * ψ i - ψ (i - 1) - ψ (i + 1))
  map_add' ψ φ := by ext i; simp; ring
  map_smul' a ψ := by ext i; simp; ring

omit [NeZero N] in
theorem cyclicLaplacian_single (w : ℝ) (k : ZMod N) :
    cyclicLaplacian w (EuclideanSpace.single k 1) =
      (w : ℂ) • ((EuclideanSpace.single k 1 - EuclideanSpace.single (k + 1) 1) +
        (EuclideanSpace.single k 1 - EuclideanSpace.single (k - 1) 1)) := by
  ext i
  have hleft : i - 1 = k ↔ i = k + 1 := sub_eq_iff_eq_add
  have hright : i + 1 = k ↔ i = k - 1 := eq_sub_iff_add_eq.symm
  simp [cyclicLaplacian, PiLp.single_apply, hleft, hright]
  split_ifs <;> ring

/-- The eigenvalue of the weighted cyclic Laplacian at Fourier label q. -/
def cyclicLaplacianEigenvalue (w : ℝ) (q : ZMod N) : ℝ :=
  2 * w * (1 - Real.cos (2 * Real.pi * (q.val / N)))

private theorem phase_sum (q : ZMod N) :
    ZMod.stdAddChar q + ZMod.stdAddChar (-q) =
      (2 * Real.cos (2 * Real.pi * (q.val / N)) : ℝ) := by
  let θ : ℝ := 2 * Real.pi * (q.val / N)
  have he : ZMod.stdAddChar q = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_eq_circleExp, Circle.coe_exp]
  rw [← ZMod.stdAddChar_conj, he, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I,
    Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

theorem cyclicLaplacian_fourierMode (w : ℝ) (q : ZMod N) :
    cyclicLaplacian w (ZMod.fourierMode q) =
      (cyclicLaplacianEigenvalue w q : ℂ) • ZMod.fourierMode q := by
  ext j
  change (w : ℂ) * (2 * ZMod.fourierMode q j - ZMod.fourierMode q (j - 1) -
    ZMod.fourierMode q (j + 1)) = _
  have hp := phase_sum q
  simp only [ZMod.fourierMode, PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul,
    mul_add, mul_one, sub_eq_add_neg, AddChar.map_add_eq_mul,
    mul_neg]
  simp only [cyclicLaplacianEigenvalue, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_ofNat, Complex.ofReal_one] at *
  linear_combination -(w : ℂ) * (Real.sqrt N : ℂ)⁻¹ * ZMod.stdAddChar (q * j) * hp

/-- The complete normalized Fourier basis diagonalizes the weighted cyclic Laplacian. -/
theorem cyclicLaplacian_fourierBasis (w : ℝ) (q : ZMod N) :
    cyclicLaplacian w (ZMod.fourierBasis q) =
      (cyclicLaplacianEigenvalue w q : ℂ) • ZMod.fourierBasis q := by
  simpa only [ZMod.fourierBasis_apply] using cyclicLaplacian_fourierMode w q

omit [NeZero N] in
theorem cyclicLaplacianEigenvalue_nonneg (w : ℝ) (hw : 0 ≤ w) (q : ZMod N) :
    0 ≤ cyclicLaplacianEigenvalue w q := by
  unfold cyclicLaplacianEigenvalue
  exact mul_nonneg (mul_nonneg (by norm_num) hw) (sub_nonneg.mpr (Real.cos_le_one _))

omit [NeZero N] in
theorem cyclicLaplacianEigenvalue_zero (w : ℝ) : cyclicLaplacianEigenvalue (N := N) w 0 = 0 := by
  simp [cyclicLaplacianEigenvalue]

theorem cyclicLaplacianEigenvalue_pos (w : ℝ) (hw : 0 < w) (q : ZMod N) (hq : q ≠ 0) :
    0 < cyclicLaplacianEigenvalue w q := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hqv : (0 : ℝ) < q.val := by
    exact_mod_cast Nat.pos_of_ne_zero ((ZMod.val_eq_zero q).not.mpr hq)
  have hqN : (q.val : ℝ) < N := by exact_mod_cast q.val_lt
  have ht : 0 < 2 * Real.pi * (q.val / N) := by positivity
  have hlt : 2 * Real.pi * (q.val / N) < 2 * Real.pi := by
    have := (div_lt_one hN).mpr hqN
    nlinarith [Real.pi_pos]
  have hc : Real.cos (2 * Real.pi * (q.val / N)) ≠ 1 := by
    intro heq
    exact ht.ne' ((Real.cos_eq_one_iff_of_lt_of_lt (by nlinarith [Real.pi_pos]) hlt).mp heq)
  unfold cyclicLaplacianEigenvalue
  exact mul_pos (mul_pos (by norm_num) hw)
    (sub_pos.mpr (lt_of_le_of_ne (Real.cos_le_one _) hc))

end
end ZMod
