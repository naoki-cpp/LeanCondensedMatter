import LeanCondensedMatter.QuantumTheory.Gibbs.Variational

/-!
# Equality cases for Gibbs variational inequalities

This file isolates the strict scalar and operator-positivity steps needed to characterize equality
in the Gibbs–Klein free-energy bound. Operator-level equality and uniqueness of the Gibbs minimizer
are developed on top of these reusable lemmas.
-/

/-- Gibbs' scalar inequality is strict unless the two positive weights agree. -/
theorem gibbs_scalar_ineq_strict (x y : ℝ) (hx : 0 ≤ x) (hy : 0 < y) (hxy : x ≠ y) :
    Real.negMulLog x + x - y < -x * Real.log y := by
  rcases eq_or_lt_of_le hx with hx0 | hx0
  · subst x
    simp only [Real.negMulLog]
    linarith
  · have hratio_pos : 0 < y / x := div_pos hy hx0
    have hratio_ne : y / x ≠ 1 := by
      intro hratio
      apply hxy
      exact ((div_eq_one_iff_eq hx0.ne').mp hratio).symm
    have hlog := Real.log_lt_sub_one_of_pos hratio_pos hratio_ne
    rw [Real.log_div hy.ne' hx0.ne'] at hlog
    have hcancel : x * (y / x) = y := by field_simp
    have hmul := mul_lt_mul_of_pos_left hlog hx0
    simp only [Real.negMulLog]
    nlinarith [hmul, hcancel]

/-- Equality in Gibbs' scalar inequality holds exactly on the diagonal `x = y`. -/
theorem gibbs_scalar_ineq_eq_iff (x y : ℝ) (hx : 0 ≤ x) (hy : 0 < y) :
    Real.negMulLog x + x - y = -x * Real.log y ↔ x = y := by
  constructor
  · intro heq
    by_contra hxy
    exact (ne_of_lt (gibbs_scalar_ineq_strict x y hx hy hxy)) heq
  · rintro rfl
    simp [Real.negMulLog]

namespace QuantumTheory

open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The Gibbs operator has a strictly positive diagonal matrix element on every unit vector.

The conclusion uses the complex positive order directly: it asserts both that the matrix element is
real and that its real value is strictly positive, rather than merely projecting it with `.re`. -/
theorem gibbsOp_diagonal_pos_of_norm_eq_one (Hop : Observable H) (β : ℝ) (v : H)
    (hv : ‖v‖ = 1) :
    (0 : ℂ) < inner ℂ v (gibbsOp Hop β v) := by
  rw [lt_iff_le_and_ne]
  refine ⟨(gibbsOp_isPositive Hop β).inner_nonneg_right v, ?_⟩
  intro hzero
  have hpb := exp_neg_beta_energy_le_gibbs_diagonal Hop β v hv
  rw [← hzero] at hpb
  exact (not_le_of_gt (Real.exp_pos _)) (by simpa using hpb)

/-- Every vector in an orthonormal family has a strictly positive Gibbs diagonal weight. -/
theorem gibbsOp_diagonal_pos_of_orthonormal (Hop : Observable H) (β : ℝ)
    {ι : Type*} {d : ι → H} (hd : Orthonormal ℂ d) (i : ι) :
    (0 : ℂ) < inner ℂ (d i) (gibbsOp Hop β (d i)) :=
  gibbsOp_diagonal_pos_of_norm_eq_one Hop β (d i) (hd.1 i)

end QuantumTheory
