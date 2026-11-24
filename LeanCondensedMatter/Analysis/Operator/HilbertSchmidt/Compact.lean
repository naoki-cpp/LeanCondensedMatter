import LeanCondensedMatter.Analysis.Operator.Compact
import LeanCondensedMatter.Analysis.Operator.HilbertSchmidt.Norm
import Mathlib.Analysis.Normed.Group.FunctionSeries

set_option linter.style.header false

/-!
# Compactness of Hilbert--Schmidt operators

Hilbert--Schmidt operators are compact. The proof approximates an operator in operator norm by
finite sums of rank-one operators obtained from a Hilbert basis.
-/

noncomputable section

open Filter Topology

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace IsHilbertSchmidt

private noncomputable def finiteRangeApprox {ι : Type*} (d : HilbertBasis ι ℂ H)
    (T : H →L[ℂ] H) (s : Finset ι) : H →L[ℂ] H :=
  ∑ i ∈ s, InnerProductSpace.rankOne ℂ (d i) ((ContinuousLinearMap.adjoint T) (d i))

private theorem finiteRangeApprox_isCompact {ι : Type*} (d : HilbertBasis ι ℂ H)
    (T : H →L[ℂ] H) (s : Finset ι) :
    IsCompactOperator (finiteRangeApprox d T s) := by
  change finiteRangeApprox d T s ∈ compactOperator (RingHom.id ℂ) H H
  exact Submodule.sum_mem _ fun i _ =>
    InnerProductSpace.isCompactOperator_rankOne (d i) ((ContinuousLinearMap.adjoint T) (d i))

private theorem inner_finiteRangeApprox_apply {ι : Type*} [DecidableEq ι]
    (d : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) (s : Finset ι) (x : H) (j : ι) :
    inner ℂ (d j) ((finiteRangeApprox d T s) x) =
      if j ∈ s then inner ℂ (d j) (T x) else 0 := by
  have happ :
      (finiteRangeApprox d T s) x =
        ∑ i ∈ s, inner ℂ ((ContinuousLinearMap.adjoint T) (d i)) x • d i := by
    simp [finiteRangeApprox, InnerProductSpace.rankOne_apply]
  rw [happ]
  simp [inner_sum, inner_smul_right, orthonormal_iff_ite.mp d.orthonormal,
    ContinuousLinearMap.adjoint_inner_left]

private theorem norm_sub_finiteRangeApprox_sq_le {ι : Type*} (d : HilbertBasis ι ℂ H)
    {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) (s : Finset ι) (x : H) :
    ‖(T - finiteRangeApprox d T s) x‖ ^ 2 ≤
      (∑' i : {j // j ∉ s}, ‖(ContinuousLinearMap.adjoint T) (d i)‖ ^ 2) * ‖x‖ ^ 2 := by
  classical
  have hparse :
      HasSum
        (fun i : ι => ‖(inner ℂ (d i) ((T - finiteRangeApprox d T s) x) : ℂ)‖ ^ 2)
        (‖(T - finiteRangeApprox d T s) x‖ ^ 2) := by
    simpa only [show (2 : ENNReal).toReal = (2 : ℝ) by norm_num, Real.rpow_two,
      d.repr_apply_apply, d.repr.norm_map] using
      (lp.hasSum_norm (p := 2) (by norm_num) (d.repr ((T - finiteRangeApprox d T s) x)))
  have hzero :
      ∑ i ∈ s, ‖(inner ℂ (d i) ((T - finiteRangeApprox d T s) x) : ℂ)‖ ^ 2 = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [sub_apply, inner_sub_right, inner_finiteRangeApprox_apply, hi]
  have htail := s.hasSum_iff_compl.mp hparse
  rw [hzero, sub_zero] at htail
  have hadj :
      Summable (fun i : {j // j ∉ s} => ‖(ContinuousLinearMap.adjoint T) (d i)‖ ^ 2) :=
    ((isHilbertSchmidt_adjoint hT).summable_norm_sq_apply d).subtype _
  refine hasSum_le (fun i => ?_) htail (hadj.hasSum.mul_right (‖x‖ ^ 2))
  rw [sub_apply, inner_sub_right, inner_finiteRangeApprox_apply, if_neg i.2, sub_zero,
    ← ContinuousLinearMap.adjoint_inner_left T x (d i), ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (norm_inner_le_norm ((ContinuousLinearMap.adjoint T) (d i)) x) 2

private theorem norm_sub_finiteRangeApprox_le {ι : Type*} (d : HilbertBasis ι ℂ H)
    {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) (s : Finset ι) :
    ‖T - finiteRangeApprox d T s‖ ≤
      Real.sqrt (∑' i : {j // j ∉ s}, ‖(ContinuousLinearMap.adjoint T) (d i)‖ ^ 2) := by
  classical
  let tail : ℝ :=
    ∑' i : {j // j ∉ s}, ‖(ContinuousLinearMap.adjoint T) (d i)‖ ^ 2
  have htail : 0 ≤ tail := tsum_nonneg fun _ => sq_nonneg _
  refine (T - finiteRangeApprox d T s).opNorm_le_bound (Real.sqrt_nonneg tail) fun x => ?_
  rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg tail) (norm_nonneg x)),
    mul_pow, Real.sq_sqrt htail]
  simpa [tail] using norm_sub_finiteRangeApprox_sq_le d hT s x

/-- Every Hilbert--Schmidt operator is compact. -/
theorem isCompact {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) :
    IsCompactOperator T := by
  classical
  obtain ⟨ι, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  let tail : Finset ι → ℝ := fun s =>
    ∑' i : {j // j ∉ s}, ‖(ContinuousLinearMap.adjoint T) (d i)‖ ^ 2
  have htail : Tendsto tail atTop (𝓝 0) := by
    simpa [tail] using
      (tendsto_tsum_compl_atTop_zero
        (fun i : ι => ‖(ContinuousLinearMap.adjoint T) (d i)‖ ^ 2))
  have hsqrt : Tendsto (fun s => Real.sqrt (tail s)) atTop (𝓝 0) := by
    simpa using htail.sqrt
  have happ : Tendsto (finiteRangeApprox d T) atTop (𝓝 T) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    refine squeeze_zero (fun s => norm_nonneg _) (fun s => ?_) hsqrt
    simpa [norm_sub_rev, tail] using norm_sub_finiteRangeApprox_le d hT s
  exact isCompactOperator_of_tendsto happ
    (Filter.Eventually.of_forall (finiteRangeApprox_isCompact d T))

end IsHilbertSchmidt

end ContinuousLinearMap
