import LeanCondensedMatter.QuantumTheory.Gibbs.Variational
import LeanCondensedMatter.Analysis.Operator.TraceClass.Equality

/-!
# Equality cases for Gibbs variational inequalities

This file isolates the strict scalar and operator-positivity steps needed to characterize equality
in the Gibbs–Klein free-energy bound. Operator-level equality and uniqueness of the Gibbs minimizer
are developed on top of these reusable lemmas.
-/

/-- Equality in Gibbs' scalar inequality holds exactly on the diagonal `x = y`. -/
theorem gibbs_scalar_ineq_eq_iff (x y : ℝ) (hx : 0 ≤ x) (hy : 0 < y) :
    Real.negMulLog x + x - y = -x * Real.log y ↔ x = y := by
  constructor
  · intro heq
    by_contra hxy
    have hlt : Real.negMulLog x + x - y < -x * Real.log y := by
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
    exact (ne_of_lt hlt) heq
  · rintro rfl
    simp [Real.negMulLog]

namespace QuantumTheory

open ContinuousLinearMap
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
  have hdiag_zero :
      diagonalExpectationValue
        (gibbsOp Hop β) (gibbsOp_isPositive Hop β).isSelfAdjoint v = 0 := by
    apply Complex.ofReal_injective
    rw [coe_diagonalExpectationValue_right]
    exact hzero.symm
  rw [hdiag_zero] at hpb
  exact (not_le_of_gt (Real.exp_pos _)) (by simpa using hpb)

/-- If an orthonormal family saturates the Gibbs spectral trace, its span has trivial orthogonal
complement. -/
theorem gibbsOp_orthogonal_span_eq_bot_of_diagonal_sum_eq_spectralTrace
    (Hop : Observable H) (β : ℝ)
    (hcompact : IsCompactOperator (gibbsOp Hop β))
    {ι : Type*} {d : ι → H} (hd : Orthonormal ℂ d)
    (heq : ∑' i, diagonalExpectationValue
        (gibbsOp Hop β) (gibbsOp_isPositive Hop β).isSelfAdjoint (d i) =
      spectralTrace (gibbsOp Hop β)) :
    (Submodule.span ℂ (Set.range d))ᗮ = ⊥ := by
  let hsummable : HasSummableRealEigenvalues (gibbsOp Hop β) :=
    gibbsOp_hasSummableRealEigenvalues_of_isCompact Hop β hcompact
  apply
    ContinuousLinearMap.orthogonal_span_eq_bot_of_sum_diagonalExpectationValue_eq_spectralTrace
      hcompact (gibbsOp_isPositive Hop β) hsummable hd ?_ heq
  intro v hv
  have hpos := gibbsOp_diagonal_pos_of_norm_eq_one Hop β v hv
  rw [← coe_diagonalExpectationValue_right
    (gibbsOp Hop β) (gibbsOp_isPositive Hop β).isSelfAdjoint v] at hpos
  exact_mod_cast hpos

end QuantumTheory
