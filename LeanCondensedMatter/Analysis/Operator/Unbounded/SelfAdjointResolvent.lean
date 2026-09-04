import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Completeness
import Mathlib.Topology.Sequences
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Resolvent estimates for unbounded self-adjoint operators

This module starts the operator-theoretic infrastructure needed for Stone's theorem.

For a symmetric partially defined operator `A` on a complex Hilbert space and a nonreal scalar
`z`, the shifted map `A - z` is bounded below on the domain by `|im z|`. For a self-adjoint
operator the same estimate gives injectivity, and closedness of the graph then implies that the
range of every nonreal shift is closed. Self-adjoint maximality forces the orthogonal complement
of that range to vanish, so the range is dense and hence, being closed, all of the Hilbert space.
Thus every nonreal shift is bijective. This is the analytic input for constructing the bounded
resolvent and, later, the Cayley-transform / Stone-theorem layer tracked by issue #840.
-/

namespace LinearPMap

noncomputable section

open Complex Filter Set
open scoped InnerProductSpace Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {A : H →ₗ.[ℂ] H}

/-- The domain-level linear map `x ↦ A x - z x` associated with a partial operator. -/
def shiftDomainMap (A : H →ₗ.[ℂ] H) (z : ℂ) : A.domain →ₗ[ℂ] H :=
  A.toFun - z • A.domain.subtype

@[simp]
theorem shiftDomainMap_apply (A : H →ₗ.[ℂ] H) (z : ℂ) (x : A.domain) :
    shiftDomainMap A z x = A x - z • (x : H) := by
  rfl

/-- For a symmetric partial operator, the quadratic form `⟪x, A x⟫` is real on the domain. -/
theorem IsFormalAdjoint.im_inner_self_apply_eq_zero
    (hA : A.IsFormalAdjoint A) (x : A.domain) :
    (inner ℂ (x : H) (A x)).im = 0 := by
  have hsymm : inner ℂ (A x) (x : H) = inner ℂ (x : H) (A x) := hA x x
  have himsymm := inner_im_symm (𝕜 := ℂ) (A x) (x : H)
  change
    (inner ℂ (A x) (x : H)).im = -(inner ℂ (x : H) (A x)).im at himsymm
  have heqim := congrArg Complex.im hsymm
  linarith

/-- A symmetric partial operator shifted by `z` is bounded below by `|im z|` on its domain.

This estimate is the elementary resolvent inequality
`|im z| ‖x‖ ≤ ‖A x - z x‖`. It does not require closedness or self-adjoint maximality; symmetry
alone is enough. -/
theorem IsFormalAdjoint.abs_im_mul_norm_le_norm_sub_smul
    (hA : A.IsFormalAdjoint A) (z : ℂ) (x : A.domain) :
    |z.im| * ‖(x : H)‖ ≤ ‖A x - z • (x : H)‖ := by
  have hself :
      inner ℂ (x : H) (x : H) = ((‖(x : H)‖ ^ 2 : ℝ) : ℂ) := by
    simpa using inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (x : H)
  have hinner_im :
      (inner ℂ (x : H) (A x - z • (x : H))).im =
        -z.im * ‖(x : H)‖ ^ 2 := by
    rw [inner_sub_right, inner_smul_right, hself]
    change
      (inner ℂ (x : H) (A x)).im -
          (z * ((‖(x : H)‖ ^ 2 : ℝ) : ℂ)).im =
        -z.im * ‖(x : H)‖ ^ 2
    rw [hA.im_inner_self_apply_eq_zero x]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_add, zero_sub]
    ring
  have habs :
      |(inner ℂ (x : H) (A x - z • (x : H))).im| =
        |z.im| * ‖(x : H)‖ ^ 2 := by
    rw [hinner_im, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg ‖(x : H)‖)]
  have hcs :
      |z.im| * ‖(x : H)‖ ^ 2 ≤
        ‖(x : H)‖ * ‖A x - z • (x : H)‖ := by
    calc
      |z.im| * ‖(x : H)‖ ^ 2 =
          |(inner ℂ (x : H) (A x - z • (x : H))).im| := habs.symm
      _ ≤ ‖inner ℂ (x : H) (A x - z • (x : H))‖ :=
        Complex.abs_im_le_norm _
      _ ≤ ‖(x : H)‖ * ‖A x - z • (x : H)‖ :=
        norm_inner_le_norm _ _
  by_cases hx : ‖(x : H)‖ = 0
  · simp [hx]
  · have hxpos : 0 < ‖(x : H)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
    nlinarith [hcs]

variable [CompleteSpace H]

/-- Self-adjoint specialization of the nonreal-shift lower bound. -/
theorem isSelfAdjoint_abs_im_mul_norm_le_norm_sub_smul
    (hA : IsSelfAdjoint A) (z : ℂ) (x : A.domain) :
    |z.im| * ‖(x : H)‖ ≤ ‖A x - z • (x : H)‖ := by
  have hadj : A.adjoint = A := LinearPMap.isSelfAdjoint_def.mp hA
  have hformal : A.IsFormalAdjoint A := by
    simpa only [hadj] using LinearPMap.adjoint_isFormalAdjoint hA.dense_domain
  exact hformal.abs_im_mul_norm_le_norm_sub_smul z x

/-- A nonreal shift of a self-adjoint operator has trivial kernel on its domain. -/
theorem isSelfAdjoint_sub_smul_eq_zero_iff
    (hA : IsSelfAdjoint A) {z : ℂ} (hz : z.im ≠ 0) (x : A.domain) :
    A x - z • (x : H) = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have hbound := isSelfAdjoint_abs_im_mul_norm_le_norm_sub_smul hA z x
    rw [hx, norm_zero] at hbound
    have himpos : 0 < |z.im| := abs_pos.mpr hz
    have hnorm : ‖(x : H)‖ = 0 := by nlinarith [norm_nonneg (x : H)]
    exact Subtype.ext (norm_eq_zero.mp hnorm)
  · rintro rfl
    simp

/-- The domain-level nonreal shift of a self-adjoint operator is injective. -/
theorem isSelfAdjoint_shiftDomainMap_injective
    (hA : IsSelfAdjoint A) {z : ℂ} (hz : z.im ≠ 0) :
    Function.Injective (shiftDomainMap A z) := by
  intro x y hxy
  have hzero : shiftDomainMap A z (x - y) = 0 := by
    calc
      shiftDomainMap A z (x - y) = shiftDomainMap A z x - shiftDomainMap A z y := by
        exact (shiftDomainMap A z).map_sub x y
      _ = 0 := sub_eq_zero.mpr hxy
  have hsub : A (x - y) - z • ((x - y : A.domain) : H) = 0 := by
    simpa only [shiftDomainMap_apply] using hzero
  have hxy0 : x - y = 0 :=
    (isSelfAdjoint_sub_smul_eq_zero_iff hA hz (x - y)).mp hsub
  exact sub_eq_zero.mp hxy0

/-- The range of a nonreal shift of a self-adjoint operator is closed.

If `(A - z) xₙ` converges, the nonreal-shift lower bound makes `xₙ` a Cauchy sequence. Completeness
provides a limit `x`, and the closed graph of the self-adjoint operator recovers `x ∈ D(A)` together
with the limiting value of `A x`. -/
theorem isSelfAdjoint_shiftDomainMap_range_isClosed
    (hA : IsSelfAdjoint A) {z : ℂ} (hz : z.im ≠ 0) :
    _root_.IsClosed (Set.range (shiftDomainMap A z)) := by
  rw [← isSeqClosed_iff_isClosed]
  intro u y hu huy
  choose x hx using hu
  have huCauchy : CauchySeq u := huy.cauchySeq
  have himpos : 0 < |z.im| := abs_pos.mpr hz
  have hxCauchy : CauchySeq (fun n => (x n : H)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ :=
      (Metric.cauchySeq_iff.mp huCauchy) (|z.im| * ε) (mul_pos himpos hε)
    refine ⟨N, ?_⟩
    intro m hm n hn
    have hbound :=
      isSelfAdjoint_abs_im_mul_norm_le_norm_sub_smul hA z (x m - x n)
    have hshift : shiftDomainMap A z (x m - x n) = u m - u n := by
      rw [(shiftDomainMap A z).map_sub, hx m, hx n]
    have hbound' :
        |z.im| * dist (x m : H) (x n : H) ≤ dist (u m) (u n) := by
      calc
        |z.im| * dist (x m : H) (x n : H) =
            |z.im| * ‖(((x m - x n : A.domain) : H))‖ := by
              simp only [dist_eq_norm, Submodule.coe_sub]
        _ ≤ ‖shiftDomainMap A z (x m - x n)‖ := by
          simpa only [shiftDomainMap_apply] using hbound
        _ = dist (u m) (u n) := by
          rw [hshift, dist_eq_norm]
    have hlt :
        |z.im| * dist (x m : H) (x n : H) < |z.im| * ε :=
      lt_of_le_of_lt hbound' (hN m hm n hn)
    nlinarith [hlt]
  obtain ⟨xlim, hxlim⟩ := cauchySeq_tendsto_of_complete hxCauchy
  have hAeq : ∀ n, A (x n) = u n + z • (x n : H) := by
    intro n
    have hn := hx n
    rw [shiftDomainMap_apply] at hn
    rw [← hn]
    abel
  have hAseq : Tendsto (fun n => A (x n)) atTop (𝓝 (y + z • xlim)) := by
    exact (huy.add (hxlim.const_smul z)).congr'
      (Eventually.of_forall fun n => (hAeq n).symm)
  have hpair :
      Tendsto (fun n => ((x n : H), A (x n))) atTop (𝓝 (xlim, y + z • xlim)) :=
    hxlim.prodMk_nhds hAseq
  have hgraph : (xlim, y + z • xlim) ∈ A.graph := by
    apply hA.isClosed.mem_of_tendsto hpair
    exact Eventually.of_forall fun n => (A.mem_graph_iff').2 ⟨x n, rfl⟩
  obtain ⟨xdom, hxdom⟩ := (A.mem_graph_iff').1 hgraph
  have hxdom_val : (xdom : H) = xlim := congrArg Prod.fst hxdom
  have hA_val : A xdom = y + z • xlim := congrArg Prod.snd hxdom
  refine ⟨xdom, ?_⟩
  rw [shiftDomainMap_apply, hA_val, hxdom_val]
  abel

/-- The orthogonal complement of the range of a nonreal self-adjoint shift is trivial. -/
theorem isSelfAdjoint_shiftDomainMap_range_orthogonal_eq_bot
    (hA : IsSelfAdjoint A) {z : ℂ} (hz : z.im ≠ 0) :
    (LinearMap.range (shiftDomainMap A z))ᗮ = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  have hzero : ∀ x : A.domain, inner ℂ w (shiftDomainMap A z x) = 0 := by
    intro x
    exact ((LinearMap.range (shiftDomainMap A z)).mem_orthogonal' w).1 hw
      (shiftDomainMap A z x) ⟨x, rfl⟩
  have hrel : ∀ x : A.domain,
      inner ℂ (star z • w) (x : H) = inner ℂ w (A x) := by
    intro x
    have hz0 := hzero x
    rw [shiftDomainMap_apply, inner_sub_right, inner_smul_right] at hz0
    have hzrel : inner ℂ w (A x) = z * inner ℂ w (x : H) := sub_eq_zero.mp hz0
    calc
      inner ℂ (star z • w) (x : H) = z * inner ℂ w (x : H) := by
        rw [inner_smul_left]
        simp
      _ = inner ℂ w (A x) := hzrel.symm
  have hwadj : w ∈ A.adjoint.domain :=
    LinearPMap.mem_adjoint_domain_of_exists w ⟨star z • w, hrel⟩
  have hadj : A.adjoint = A := LinearPMap.isSelfAdjoint_def.mp hA
  have hwdom : w ∈ A.domain := by
    simpa only [hadj] using hwadj
  let wdom : A.domain := ⟨w, hwdom⟩
  have hformal : A.IsFormalAdjoint A := by
    simpa only [hadj] using LinearPMap.adjoint_isFormalAdjoint hA.dense_domain
  have hAw : A wdom = star z • w := by
    apply hA.dense_domain.eq_of_inner_left ℂ
    intro v hv
    let vdom : A.domain := ⟨v, hv⟩
    exact (hformal wdom vdom).trans (hrel vdom).symm
  have hshift : A wdom - star z • (wdom : H) = 0 := by
    simpa [wdom] using sub_eq_zero.mpr hAw
  have hzstar : (star z).im ≠ 0 := by
    simpa using neg_ne_zero.mpr hz
  have hwzero : wdom = 0 :=
    (isSelfAdjoint_sub_smul_eq_zero_iff hA hzstar wdom).mp hshift
  change w = 0
  simpa [wdom] using congrArg Subtype.val hwzero

/-- The range of a nonreal shift of a self-adjoint operator is dense. -/
theorem isSelfAdjoint_shiftDomainMap_range_dense
    (hA : IsSelfAdjoint A) {z : ℂ} (hz : z.im ≠ 0) :
    Dense (Set.range (shiftDomainMap A z)) := by
  change Dense ((LinearMap.range (shiftDomainMap A z) : Submodule ℂ H) : Set H)
  rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe]
  rw [(Submodule.topologicalClosure_eq_top_iff).2
    (isSelfAdjoint_shiftDomainMap_range_orthogonal_eq_bot hA hz)]
  rfl

/-- Every nonreal shift of a self-adjoint operator is surjective. -/
theorem isSelfAdjoint_shiftDomainMap_surjective
    (hA : IsSelfAdjoint A) {z : ℂ} (hz : z.im ≠ 0) :
    Function.Surjective (shiftDomainMap A z) := by
  have hclosed := isSelfAdjoint_shiftDomainMap_range_isClosed hA hz
  have hdense := isSelfAdjoint_shiftDomainMap_range_dense hA hz
  have hclosure : _root_.closure (Set.range (shiftDomainMap A z)) = Set.univ :=
    dense_iff_closure_eq.mp hdense
  have hrange : Set.range (shiftDomainMap A z) = Set.univ := by
    calc
      Set.range (shiftDomainMap A z) = _root_.closure (Set.range (shiftDomainMap A z)) :=
        hclosed.closure_eq.symm
      _ = Set.univ := hclosure
  exact Set.range_eq_univ.mp hrange

/-- Every nonreal shift of a self-adjoint operator is bijective on its operator domain. -/
theorem isSelfAdjoint_shiftDomainMap_bijective
    (hA : IsSelfAdjoint A) {z : ℂ} (hz : z.im ≠ 0) :
    Function.Bijective (shiftDomainMap A z) :=
  ⟨isSelfAdjoint_shiftDomainMap_injective hA hz,
    isSelfAdjoint_shiftDomainMap_surjective hA hz⟩

end

end LinearPMap
