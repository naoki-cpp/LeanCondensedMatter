import LeanCondensedMatter.Analysis.Operator.HilbertSchmidt.InnerProduct

set_option linter.style.header false

/-!
# Hilbert--Schmidt norm square

This module defines the basis-independent squared Hilbert--Schmidt norm. Its canonical basis
formula is exposed directly as a `tsum`, together with summability and `HasSum` theorems.
-/

noncomputable section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace IsHilbertSchmidt

/-- The basis-independent squared Hilbert--Schmidt norm. -/
noncomputable def normSq {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) : ℝ :=
  let w : Set H := Classical.choose hT
  let hw : ∃ d : HilbertBasis w ℂ H, IsHilbertSchmidtWrt d T :=
    Classical.choose_spec hT
  let d : HilbertBasis w ℂ H := Classical.choose hw
  ∑' i, ‖T (d i)‖ ^ 2

/-- The square-norm family in every Hilbert basis sums to the canonical Hilbert--Schmidt norm
square. -/
theorem hasSum_norm_sq_apply {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T)
    {ι : Type*} (d : HilbertBasis ι ℂ H) :
    HasSum (fun i => ‖T (d i)‖ ^ 2) hT.normSq := by
  unfold normSq
  exact hasSum_norm_sq_apply_of_hasSum _ d T (hT.summable_norm_sq_apply _).hasSum

/-- The squared Hilbert--Schmidt norm is the square-norm sum in every Hilbert basis. -/
theorem normSq_eq_tsum_norm_sq_apply {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T)
    {ι : Type*} (d : HilbertBasis ι ℂ H) :
    hT.normSq = ∑' i, ‖T (d i)‖ ^ 2 :=
  (hT.hasSum_norm_sq_apply d).tsum_eq.symm

omit [CompleteSpace H] in
/-- The squared Hilbert--Schmidt norm is nonnegative. -/
theorem normSq_nonneg {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) :
    0 ≤ hT.normSq := by
  unfold normSq
  exact tsum_nonneg fun _ => sq_nonneg _

/-- The squared Hilbert--Schmidt norm is strictly positive for a nonzero operator. -/
theorem normSq_pos {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) (hne : T ≠ 0) :
    0 < hT.normSq := by
  by_contra! hle
  have hzero : hT.normSq = 0 := le_antisymm hle hT.normSq_nonneg
  obtain ⟨w, b, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  have hb (i : w) : T (b i) = 0 := by
    have hterm := (hT.summable_norm_sq_apply b).le_tsum i
      (fun j _ => sq_nonneg ‖T (b j)‖)
    rw [← hT.normSq_eq_tsum_norm_sq_apply b, hzero] at hterm
    by_contra hi
    exact (not_lt_of_ge hterm) (pow_pos (norm_pos_iff.mpr hi) 2)
  apply hne
  ext x
  have hsum := (b.hasSum_repr x).mapL T
  simpa [hb] using hsum.tsum_eq.symm

/-- Taking the adjoint preserves the squared Hilbert--Schmidt norm. -/
theorem normSq_adjoint {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) :
    (isHilbertSchmidt_adjoint hT).normSq = hT.normSq := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  exact ((isHilbertSchmidt_adjoint hT).hasSum_norm_sq_apply d).unique
    (hasSum_norm_sq_adjoint_apply d d T (hT.hasSum_norm_sq_apply d))

/-- Left composition by a bounded operator increases the squared Hilbert--Schmidt norm by at most
the square of the operator norm. -/
theorem normSq_comp_left_le (hT : IsHilbertSchmidt T) (B : H →L[ℂ] H) :
    (isHilbertSchmidt_comp_left B hT).normSq ≤ ‖B‖ ^ 2 * hT.normSq := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  refine hasSum_le (fun i => ?_)
    ((isHilbertSchmidt_comp_left B hT).hasSum_norm_sq_apply d)
    ((hT.hasSum_norm_sq_apply d).mul_left (‖B‖ ^ 2))
  rw [mul_apply_eq_comp, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (B.le_opNorm (T (d i))) 2

/-- Right composition by a bounded operator increases the squared Hilbert--Schmidt norm by at most
the square of the operator norm. -/
theorem normSq_comp_right_le (hT : IsHilbertSchmidt T) (B : H →L[ℂ] H) :
    (isHilbertSchmidt_comp_right hT B).normSq ≤ ‖B‖ ^ 2 * hT.normSq := by
  have hadj_eq :
      ContinuousLinearMap.adjoint (T * B) =
        ContinuousLinearMap.adjoint B * ContinuousLinearMap.adjoint T := by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.star_eq_adjoint,
      ← ContinuousLinearMap.star_eq_adjoint, star_mul]
  have hnorm :
      (isHilbertSchmidt_comp_left (ContinuousLinearMap.adjoint B)
        (isHilbertSchmidt_adjoint hT)).normSq =
        (isHilbertSchmidt_comp_right hT B).normSq := by
    simpa only [hadj_eq] using
      (isHilbertSchmidt_comp_right hT B).normSq_adjoint
  have h := (isHilbertSchmidt_adjoint hT).normSq_comp_left_le
    (ContinuousLinearMap.adjoint B)
  rw [hnorm, hT.normSq_adjoint, ← ContinuousLinearMap.star_eq_adjoint, norm_star] at h
  exact h

/-- Right composition by a contraction does not increase the squared Hilbert--Schmidt norm. -/
theorem normSq_comp_right_le_of_norm_le_one (hT : IsHilbertSchmidt T)
    (B : H →L[ℂ] H) (hB : ‖B‖ ≤ 1) :
    (isHilbertSchmidt_comp_right hT B).normSq ≤ hT.normSq := by
  calc
    (isHilbertSchmidt_comp_right hT B).normSq ≤ ‖B‖ ^ 2 * hT.normSq :=
      hT.normSq_comp_right_le B
    _ ≤ 1 ^ 2 * hT.normSq :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg B) hB 2) hT.normSq_nonneg
    _ = hT.normSq := by rw [one_pow, one_mul]

/-- The absolute diagonal pairing of two Hilbert--Schmidt operators is summable, and its
sum is bounded by the arithmetic mean of their squared Hilbert--Schmidt norms. -/
theorem summable_norm_inner_apply_and_tsum_le {S T : H →L[ℂ] H}
    (hS : IsHilbertSchmidt S) (hT : IsHilbertSchmidt T)
    {ι : Type*} (d : HilbertBasis ι ℂ H) :
    Summable (fun i => ‖inner ℂ (S (d i)) (T (d i))‖) ∧
      ∑' i, ‖inner ℂ (S (d i)) (T (d i))‖ ≤ (hS.normSq + hT.normSq) / 2 := by
  have hsum := (hS.summable_inner_apply hT d).norm
  have hmajor :
      HasSum (fun i => (‖S (d i)‖ ^ 2 + ‖T (d i)‖ ^ 2) / 2)
        ((hS.normSq + hT.normSq) / 2) :=
    ((hS.hasSum_norm_sq_apply d).add (hT.hasSum_norm_sq_apply d)).div_const 2
  refine ⟨hsum, (hsum.tsum_le_tsum (fun i => ?_) hmajor.summable).trans_eq hmajor.tsum_eq⟩
  exact (norm_inner_le_norm (S (d i)) (T (d i))).trans (by
    nlinarith [sq_nonneg (‖S (d i)‖ - ‖T (d i)‖)])

end IsHilbertSchmidt

end ContinuousLinearMap
