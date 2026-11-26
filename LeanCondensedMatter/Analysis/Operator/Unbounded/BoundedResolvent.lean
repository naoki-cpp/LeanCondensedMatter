import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Completeness
import Mathlib.Topology.Sequences
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Tactic.Module
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option linter.style.header false

/-!
# Nonreal resolvents of unbounded self-adjoint operators

For a symmetric partially defined operator on a complex Hilbert space, the nonreal shift is
bounded below by `|im z|` on its domain. For a self-adjoint operator, its graph is closed and
self-adjoint maximality makes the range dense, so the shift is bijective. Its inverse is a
continuous linear map into the operator domain with pointwise norm bound `|im z|⁻¹`.
Composition with the domain inclusion yields the bounded resolvent `R(z) = (A - z)⁻¹`.
The inverse identities give the resolvent identity and pairwise commutation. The adjoint is
the resolvent at the conjugate spectral parameter, and the associated Cayley transform
`1 + (z - star z) • R(z)` is unitary. These results supply the bounded approximation theory
used in the Stone construction.
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
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  exact (isSelfAdjoint_sub_smul_eq_zero_iff hA hz x).mp (by
    simpa only [shiftDomainMap_apply] using hx)

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
  rw [← Set.range_eq_univ, ← (isSelfAdjoint_shiftDomainMap_range_isClosed hA hz).closure_eq]
  exact dense_iff_closure_eq.mp (isSelfAdjoint_shiftDomainMap_range_dense hA hz)

/-- Every nonreal shift of a self-adjoint operator is bijective on its operator domain. -/
theorem isSelfAdjoint_shiftDomainMap_bijective
    (hA : IsSelfAdjoint A) {z : ℂ} (hz : z.im ≠ 0) :
    Function.Bijective (shiftDomainMap A z) :=
  ⟨isSelfAdjoint_shiftDomainMap_injective hA hz,
    isSelfAdjoint_shiftDomainMap_surjective hA hz⟩

end

end LinearPMap

namespace LinearPMap

noncomputable section

open Complex
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A nonreal shift of a self-adjoint operator, viewed as a linear equivalence from its domain onto
all of the ambient Hilbert space. -/
noncomputable def nonrealShiftLinearEquiv
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (z : ℂ) (hz : z.im ≠ 0) :
    A.domain ≃ₗ[ℂ] H :=
  LinearEquiv.ofBijective (shiftDomainMap A z)
    (isSelfAdjoint_shiftDomainMap_bijective hA hz)

@[simp]
theorem nonrealShiftLinearEquiv_apply
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (z : ℂ) (hz : z.im ≠ 0)
    (x : A.domain) :
    nonrealShiftLinearEquiv A hA z hz x = A x - z • (x : H) := by
  rfl

private theorem nonrealShiftLinearEquiv_symm_norm_le
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (z : ℂ) (hz : z.im ≠ 0) (y : H) :
    ‖(nonrealShiftLinearEquiv A hA z hz).symm y‖ ≤ |z.im|⁻¹ * ‖y‖ := by
  let e := nonrealShiftLinearEquiv A hA z hz
  let x : A.domain := e.symm y
  have hbound := isSelfAdjoint_abs_im_mul_norm_le_norm_sub_smul hA z x
  have hright : shiftDomainMap A z x = y := by
    exact e.apply_symm_apply y
  have hright' : A x - z • (x : H) = y := by
    simpa only [shiftDomainMap_apply] using hright
  rw [hright'] at hbound
  have himpos : 0 < |z.im| := abs_pos.mpr hz
  have hdiv : ‖(x : H)‖ ≤ ‖y‖ / |z.im| := by
    apply (le_div_iff₀ himpos).2
    simpa [mul_comm] using hbound
  simpa [e, x, div_eq_mul_inv, mul_comm] using hdiv

/-- The inverse nonreal shift, bundled as a continuous linear map into the operator domain. -/
noncomputable def nonrealShiftInverseDomain
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (z : ℂ) (hz : z.im ≠ 0) :
    H →L[ℂ] A.domain :=
  (nonrealShiftLinearEquiv A hA z hz).symm.toLinearMap.mkContinuous |z.im|⁻¹
    (nonrealShiftLinearEquiv_symm_norm_le A hA z hz)

@[simp]
theorem nonrealShiftInverseDomain_apply
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (z : ℂ) (hz : z.im ≠ 0) (y : H) :
    nonrealShiftInverseDomain A hA z hz y =
      (nonrealShiftLinearEquiv A hA z hz).symm y := by
  rfl

/-- Applying the shifted operator to its domain-valued bounded inverse gives the identity. -/
theorem shiftDomainMap_nonrealShiftInverseDomain
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (z : ℂ) (hz : z.im ≠ 0) (y : H) :
    shiftDomainMap A z (nonrealShiftInverseDomain A hA z hz y) = y := by
  change nonrealShiftLinearEquiv A hA z hz
      ((nonrealShiftLinearEquiv A hA z hz).symm y) = y
  exact (nonrealShiftLinearEquiv A hA z hz).apply_symm_apply y

/-- The bounded inverse obeys the standard nonreal resolvent estimate pointwise. -/
theorem norm_nonrealShiftInverseDomain_le
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (z : ℂ) (hz : z.im ≠ 0) (y : H) :
    ‖nonrealShiftInverseDomain A hA z hz y‖ ≤ |z.im|⁻¹ * ‖y‖ := by
  simpa only [nonrealShiftInverseDomain_apply] using
    nonrealShiftLinearEquiv_symm_norm_le A hA z hz y

/-- The bounded resolvent `(A - z)⁻¹` as an operator on the ambient Hilbert space. -/
noncomputable def nonrealResolvent
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (z : ℂ) (hz : z.im ≠ 0) :
    H →L[ℂ] H :=
  A.domain.subtypeL.comp (nonrealShiftInverseDomain A hA z hz)

@[simp]
theorem nonrealResolvent_apply
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (z : ℂ) (hz : z.im ≠ 0) (y : H) :
    nonrealResolvent A hA z hz y =
      (nonrealShiftInverseDomain A hA z hz y : H) := by
  rfl

/-- Pointwise norm estimate for the bounded nonreal resolvent. -/
theorem norm_nonrealResolvent_le
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (z : ℂ) (hz : z.im ≠ 0) (y : H) :
    ‖nonrealResolvent A hA z hz y‖ ≤ |z.im|⁻¹ * ‖y‖ := by
  change ‖nonrealShiftInverseDomain A hA z hz y‖ ≤ |z.im|⁻¹ * ‖y‖
  exact norm_nonrealShiftInverseDomain_le A hA z hz y

/-- The resolvent value lies in the original unbounded operator domain. -/
theorem nonrealResolvent_mem_domain
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (z : ℂ) (hz : z.im ≠ 0) (y : H) :
    nonrealResolvent A hA z hz y ∈ A.domain :=
  (nonrealShiftInverseDomain A hA z hz y).property

/-- The bounded resolvent is a right inverse of the nonreal shift. -/
theorem apply_nonrealResolvent_sub_smul
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (z : ℂ) (hz : z.im ≠ 0) (y : H) :
    A ⟨nonrealResolvent A hA z hz y,
        nonrealResolvent_mem_domain A hA z hz y⟩ -
      z • nonrealResolvent A hA z hz y = y := by
  simpa only [nonrealResolvent_apply, shiftDomainMap_apply] using
    shiftDomainMap_nonrealShiftInverseDomain A hA z hz y

/-- The bounded resolvent is also a left inverse of the nonreal shift on the original domain. -/
theorem nonrealResolvent_shift_apply
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (z : ℂ) (hz : z.im ≠ 0)
    (x : A.domain) :
    nonrealResolvent A hA z hz (A x - z • (x : H)) = (x : H) := by
  let e := nonrealShiftLinearEquiv A hA z hz
  have h := e.symm_apply_apply x
  have he : e x = A x - z • (x : H) := by
    exact nonrealShiftLinearEquiv_apply A hA z hz x
  have hval := congrArg Subtype.val h
  simpa [e, nonrealResolvent_apply, nonrealShiftInverseDomain_apply, he] using hval

/-- Resolvents commute with applying the generator on its domain in the expected affine form. -/
theorem nonrealResolvent_apply_operator
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (z : ℂ) (hz : z.im ≠ 0)
    (x : A.domain) :
    nonrealResolvent A hA z hz (A x) =
      (x : H) + z • nonrealResolvent A hA z hz (x : H) := by
  have h := nonrealResolvent_shift_apply A hA z hz x
  rw [(nonrealResolvent A hA z hz).map_sub,
    (nonrealResolvent A hA z hz).map_smul] at h
  exact sub_eq_iff_eq_add.mp h

/-- Pointwise resolvent identity for the convention `R(z) = (A-z)⁻¹`. -/
theorem nonrealResolvent_sub_nonrealResolvent_apply
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) (y : H) :
    nonrealResolvent A hA z hz y - nonrealResolvent A hA w hw y =
      (z - w) • nonrealResolvent A hA z hz (nonrealResolvent A hA w hw y) := by
  let x : A.domain :=
    ⟨nonrealResolvent A hA w hw y, nonrealResolvent_mem_domain A hA w hw y⟩
  have hy : A x - w • (x : H) = y := by
    simpa [x] using apply_nonrealResolvent_sub_smul A hA w hw y
  calc
    nonrealResolvent A hA z hz y - nonrealResolvent A hA w hw y =
        nonrealResolvent A hA z hz (A x - w • (x : H)) - (x : H) := by
      rw [hy]
    _ = (nonrealResolvent A hA z hz (A x) -
          w • nonrealResolvent A hA z hz (x : H)) - (x : H) := by
      rw [(nonrealResolvent A hA z hz).map_sub,
        (nonrealResolvent A hA z hz).map_smul]
    _ = ((x : H) + z • nonrealResolvent A hA z hz (x : H) -
          w • nonrealResolvent A hA z hz (x : H)) - (x : H) := by
      rw [nonrealResolvent_apply_operator A hA z hz x]
    _ = (z - w) • nonrealResolvent A hA z hz (nonrealResolvent A hA w hw y) := by
      change ((x : H) + z • nonrealResolvent A hA z hz (x : H) -
          w • nonrealResolvent A hA z hz (x : H)) - (x : H) =
        (z - w) • nonrealResolvent A hA z hz (x : H)
      module

/-- Bounded nonreal resolvents of one self-adjoint operator commute pairwise. -/
theorem nonrealResolvent_mul_comm
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    nonrealResolvent A hA z hz * nonrealResolvent A hA w hw =
      nonrealResolvent A hA w hw * nonrealResolvent A hA z hz := by
  ext y
  by_cases hzw : z = w
  · subst w
    rfl
  · have h₁ := nonrealResolvent_sub_nonrealResolvent_apply A hA z w hz hw y
    have h₂ := nonrealResolvent_sub_nonrealResolvent_apply A hA w z hw hz y
    have hscaled :
        (z - w) • nonrealResolvent A hA z hz (nonrealResolvent A hA w hw y) =
          (z - w) • nonrealResolvent A hA w hw (nonrealResolvent A hA z hz y) := by
      calc
        (z - w) • nonrealResolvent A hA z hz (nonrealResolvent A hA w hw y) =
            nonrealResolvent A hA z hz y - nonrealResolvent A hA w hw y := h₁.symm
        _ = -(nonrealResolvent A hA w hw y - nonrealResolvent A hA z hz y) := by
          module
        _ = -((w - z) • nonrealResolvent A hA w hw
              (nonrealResolvent A hA z hz y)) := by rw [h₂]
        _ = (z - w) • nonrealResolvent A hA w hw
              (nonrealResolvent A hA z hz y) := by
          module
    have hne : z - w ≠ 0 := sub_ne_zero.mpr hzw
    have hcancel := congrArg (fun v : H => (z - w)⁻¹ • v) hscaled
    simpa [smul_smul, hne] using hcancel

/-- `Commute`-packaged form of pairwise nonreal resolvent commutation. -/
theorem nonrealResolvent_commute
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    Commute (nonrealResolvent A hA z hz) (nonrealResolvent A hA w hw) := by
  exact nonrealResolvent_mul_comm A hA z w hz hw

private theorem star_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) : (star z).im ≠ 0 := by
  simpa using neg_ne_zero.mpr hz

/-- The adjoint of a nonreal resolvent is the resolvent at the conjugate spectral parameter. -/
theorem nonrealResolvent_adjoint
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (z : ℂ) (hz : z.im ≠ 0) :
    ContinuousLinearMap.adjoint (nonrealResolvent A hA z hz) =
      nonrealResolvent A hA (star z) (star_im_ne_zero hz) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff
    (nonrealResolvent A hA (star z) (star_im_ne_zero hz))
    (nonrealResolvent A hA z hz)).2
  intro x y
  let u : A.domain := nonrealShiftInverseDomain A hA (star z) (star_im_ne_zero hz) x
  let v : A.domain := nonrealShiftInverseDomain A hA z hz y
  have hu : A u - star z • (u : H) = x := by
    simpa only [shiftDomainMap_apply] using
      shiftDomainMap_nonrealShiftInverseDomain A hA (star z) (star_im_ne_zero hz) x
  have hv : A v - z • (v : H) = y := by
    simpa only [shiftDomainMap_apply] using
      shiftDomainMap_nonrealShiftInverseDomain A hA z hz y
  have hAu : A u = x + star z • (u : H) := by
    rw [← hu]
    abel
  have hformal : A.IsFormalAdjoint A := by
    have hadj : A.adjoint = A := LinearPMap.isSelfAdjoint_def.mp hA
    simpa only [hadj] using LinearPMap.adjoint_isFormalAdjoint hA.dense_domain
  change inner ℂ (u : H) y = inner ℂ x (v : H)
  calc
    inner ℂ (u : H) y = inner ℂ (u : H) (A v - z • (v : H)) := by rw [hv]
    _ = inner ℂ (u : H) (A v) - z * inner ℂ (u : H) (v : H) := by
      rw [inner_sub_right, inner_smul_right]
    _ = inner ℂ (A u) (v : H) - z * inner ℂ (u : H) (v : H) := by
      rw [← hformal u v]
    _ = inner ℂ (x + star z • (u : H)) (v : H) -
          z * inner ℂ (u : H) (v : H) := by rw [hAu]
    _ = inner ℂ x (v : H) := by
      rw [inner_add_left, inner_smul_left]
      simp

/-- Cayley transform associated with a nonreal spectral parameter. -/
noncomputable def cayleyTransform
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (z : ℂ) (hz : z.im ≠ 0) :
    H →L[ℂ] H :=
  1 + (z - star z) • nonrealResolvent A hA z hz

@[simp]
theorem cayleyTransform_apply
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (z : ℂ) (hz : z.im ≠ 0) (y : H) :
    cayleyTransform A hA z hz y =
      y + (z - star z) • nonrealResolvent A hA z hz y := by
  rfl

/-- The Cayley transform sends `(A-z)u` to `(A-star z)u`. -/
theorem cayleyTransform_shift_apply
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (z : ℂ) (hz : z.im ≠ 0)
    (u : A.domain) :
    cayleyTransform A hA z hz (A u - z • (u : H)) =
      A u - star z • (u : H) := by
  rw [cayleyTransform_apply, nonrealResolvent_shift_apply A hA z hz u]
  module

/-- Conjugating the spectral parameter gives the adjoint Cayley transform. -/
theorem cayleyTransform_adjoint
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (z : ℂ) (hz : z.im ≠ 0) :
    ContinuousLinearMap.adjoint (cayleyTransform A hA z hz) =
      cayleyTransform A hA (star z) (star_im_ne_zero hz) := by
  change star (cayleyTransform A hA z hz) =
    cayleyTransform A hA (star z) (star_im_ne_zero hz)
  simp only [cayleyTransform, star_add, star_one, star_smul,
    ContinuousLinearMap.star_eq_adjoint, nonrealResolvent_adjoint, star_sub, star_star]

/-- The Cayley transforms at `z` and `star z` are mutual inverses in this order. -/
theorem cayleyTransform_conj_comp
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (z : ℂ) (hz : z.im ≠ 0) :
    cayleyTransform A hA (star z) (star_im_ne_zero hz) ∘L
        cayleyTransform A hA z hz = 1 := by
  apply ContinuousLinearMap.ext
  intro y
  let u : A.domain := nonrealShiftInverseDomain A hA z hz y
  have hy : A u - z • (u : H) = y := by
    simpa only [shiftDomainMap_apply] using
      shiftDomainMap_nonrealShiftInverseDomain A hA z hz y
  calc
    (cayleyTransform A hA (star z) (star_im_ne_zero hz) ∘L
        cayleyTransform A hA z hz) y =
        cayleyTransform A hA (star z) (star_im_ne_zero hz)
          (A u - star z • (u : H)) := by
            rw [ContinuousLinearMap.comp_apply, ← hy]
            rw [cayleyTransform_shift_apply]
    _ = A u - star (star z) • (u : H) := by
      rw [cayleyTransform_shift_apply]
    _ = A u - z • (u : H) := by simp
    _ = y := hy
    _ = (1 : H →L[ℂ] H) y := by rfl

/-- The Cayley transforms at `z` and `star z` are mutual inverses in the other order. -/
theorem cayleyTransform_comp_conj
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (z : ℂ) (hz : z.im ≠ 0) :
    cayleyTransform A hA z hz ∘L
        cayleyTransform A hA (star z) (star_im_ne_zero hz) = 1 := by
  simpa using cayleyTransform_conj_comp A hA (star z) (star_im_ne_zero hz)

/-- The Cayley transform is unitary: its adjoint is a left inverse. -/
theorem cayleyTransform_adjoint_comp
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (z : ℂ) (hz : z.im ≠ 0) :
    ContinuousLinearMap.adjoint (cayleyTransform A hA z hz) ∘L
        cayleyTransform A hA z hz = 1 := by
  rw [cayleyTransform_adjoint]
  exact cayleyTransform_conj_comp A hA z hz

/-- The Cayley transform is unitary: its adjoint is a right inverse. -/
theorem cayleyTransform_comp_adjoint
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (z : ℂ) (hz : z.im ≠ 0) :
    cayleyTransform A hA z hz ∘L
        ContinuousLinearMap.adjoint (cayleyTransform A hA z hz) = 1 := by
  rw [cayleyTransform_adjoint]
  exact cayleyTransform_comp_conj A hA z hz

end

end LinearPMap
