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
  classical
  unfold finiteRangeApprox
  induction s using Finset.induction_on with
  | empty =>
      simpa using (isCompactOperator_zero : IsCompactOperator (0 : H →L[ℂ] H))
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (InnerProductSpace.isCompactOperator_rankOne
        (d i) ((ContinuousLinearMap.adjoint T) (d i))).add ih

private theorem inner_finiteRangeApprox_apply_of_mem {ι : Type*} (d : HilbertBasis ι ℂ H)
    (T : H →L[ℂ] H) (s : Finset ι) (x : H) {j : ι} (hj : j ∈ s) :
    inner ℂ ((finiteRangeApprox d T s) x) (d j) = inner ℂ (T x) (d j) := by
  classical
  rw [finiteRangeApprox, Finset.sum_apply]
  simp only [InnerProductSpace.rankOne_apply]
  rw [d.orthonormal.inner_left_sum
    (fun i => inner ℂ ((ContinuousLinearMap.adjoint T) (d i)) x) hj]
  simpa only [inner_conj_symm] using
    (ContinuousLinearMap.adjoint_inner_right T x (d j))

private theorem inner_finiteRangeApprox_apply_of_not_mem {ι : Type*}
    (d : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) (s : Finset ι) (x : H)
    {j : ι} (hj : j ∉ s) :
    inner ℂ ((finiteRangeApprox d T s) x) (d j) = 0 := by
  classical
  rw [finiteRangeApprox, Finset.sum_apply, sum_inner]
  apply Finset.sum_eq_zero
  intro i hi
  have hij : i ≠ j := fun h => hj (h ▸ hi)
  rw [InnerProductSpace.inner_left_rankOne_apply, d.orthonormal.2 hij, mul_zero]

private theorem norm_sub_finiteRangeApprox_sq_le {ι : Type*} (d : HilbertBasis ι ℂ H)
    {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) (s : Finset ι) (x : H) :
    ‖(T - finiteRangeApprox d T s) x‖ ^ 2 ≤
      (∑' i : {j // j ∉ s}, ‖(ContinuousLinearMap.adjoint T) (d i)‖ ^ 2) * ‖x‖ ^ 2 := by
  classical
  let hTadj : IsHilbertSchmidt (ContinuousLinearMap.adjoint T) :=
    isHilbertSchmidt_adjoint hT
  have hparse :
      HasSum
        (fun i : ι => ‖(inner ℂ ((T - finiteRangeApprox d T s) x) (d i) : ℂ)‖ ^ 2)
        (‖(T - finiteRangeApprox d T s) x‖ ^ 2) :=
    d.hasSum_norm_sq_inner ((T - finiteRangeApprox d T s) x)
  have hzero :
      ∑ i ∈ s, ‖(inner ℂ ((T - finiteRangeApprox d T s) x) (d i) : ℂ)‖ ^ 2 = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [sub_apply, inner_sub_left,
      inner_finiteRangeApprox_apply_of_mem d T s x hi, sub_self, norm_zero, zero_pow]
    norm_num
  have hsplit := hparse.summable.sum_add_tsum_subtype_compl s
  rw [hzero, zero_add] at hsplit
  rw [← hparse.tsum_eq, ← hsplit]
  have hcoeff :
      Summable (fun i : {j // j ∉ s} =>
        ‖(inner ℂ ((T - finiteRangeApprox d T s) x) (d i) : ℂ)‖ ^ 2) :=
    hparse.summable.subtype _
  have hadj :
      Summable (fun i : ι => ‖(ContinuousLinearMap.adjoint T) (d i)‖ ^ 2) :=
    hTadj.summable_norm_sq_apply d
  have hadjCompl :
      Summable (fun i : {j // j ∉ s} =>
        ‖(ContinuousLinearMap.adjoint T) (d i)‖ ^ 2) :=
    hadj.subtype _
  have hmajor :
      Summable (fun i : {j // j ∉ s} =>
        ‖x‖ ^ 2 * ‖(ContinuousLinearMap.adjoint T) (d i)‖ ^ 2) :=
    hadjCompl.mul_left (‖x‖ ^ 2)
  calc
    (∑' i : {j // j ∉ s},
        ‖(inner ℂ ((T - finiteRangeApprox d T s) x) (d i) : ℂ)‖ ^ 2) ≤
        ∑' i : {j // j ∉ s},
          ‖x‖ ^ 2 * ‖(ContinuousLinearMap.adjoint T) (d i)‖ ^ 2 := by
      exact hcoeff.tsum_le_tsum (fun i => by
        rw [sub_apply, inner_sub_left,
          inner_finiteRangeApprox_apply_of_not_mem d T s x i.2, sub_zero]
        have hi :
            ‖(inner ℂ (T x) (d i) : ℂ)‖ ≤
              ‖x‖ * ‖(ContinuousLinearMap.adjoint T) (d i)‖ := by
          rw [← ContinuousLinearMap.adjoint_inner_right T x (d i)]
          exact norm_inner_le_norm x ((ContinuousLinearMap.adjoint T) (d i))
        calc
          ‖(inner ℂ (T x) (d i) : ℂ)‖ ^ 2 ≤
              (‖x‖ * ‖(ContinuousLinearMap.adjoint T) (d i)‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hi 2
          _ = ‖x‖ ^ 2 * ‖(ContinuousLinearMap.adjoint T) (d i)‖ ^ 2 := by ring) hmajor
    _ = ‖x‖ ^ 2 *
        ∑' i : {j // j ∉ s}, ‖(ContinuousLinearMap.adjoint T) (d i)‖ ^ 2 := by
      rw [tsum_mul_left]
    _ = (∑' i : {j // j ∉ s}, ‖(ContinuousLinearMap.adjoint T) (d i)‖ ^ 2) *
        ‖x‖ ^ 2 := by ring

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
