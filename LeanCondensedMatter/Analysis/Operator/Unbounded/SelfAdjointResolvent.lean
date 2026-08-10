import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Resolvent estimates for unbounded self-adjoint operators

This module starts the operator-theoretic infrastructure needed for Stone's theorem.

For a symmetric partially defined operator `A` on a complex Hilbert space and a nonreal scalar
`z`, the shifted map `A - z` is bounded below on the domain by `|im z|`.  In particular, a
self-adjoint operator has no nonzero vector in the kernel of a nonreal shift.  This is the first
step toward proving that the nonreal resolvent exists and is bounded, which in turn feeds the
Cayley-transform / Stone-theorem construction tracked by LeanCondensedMatter issue #840.
-/

namespace LinearPMap

noncomputable section

open Complex
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
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
  have himsymm :
      (inner ℂ (A x) (x : H)).im = -(inner ℂ (x : H) (A x)).im :=
    inner_im_symm (A x) (x : H)
  have heqim := congrArg Complex.im hsymm
  linarith

/-- A symmetric partial operator shifted by `z` is bounded below by `|im z|` on its domain.

This estimate is the elementary resolvent inequality
`|im z| ‖x‖ ≤ ‖A x - z x‖`.  It does not require closedness or self-adjoint maximality; symmetry
alone is enough. -/
theorem IsFormalAdjoint.abs_im_mul_norm_le_norm_sub_smul
    (hA : A.IsFormalAdjoint A) (z : ℂ) (x : A.domain) :
    |z.im| * ‖(x : H)‖ ≤ ‖A x - z • (x : H)‖ := by
  have hinner_im :
      (inner ℂ (x : H) (A x - z • (x : H))).im =
        -z.im * ‖(x : H)‖ ^ 2 := by
    rw [inner_sub_right, inner_smul_right]
    simp [hA.im_inner_self_apply_eq_zero x, inner_self_eq_norm_sq_to_K, Complex.mul_im]
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
    apply (mul_le_mul_left hxpos).mp
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hcs

/-- Self-adjoint specialization of the nonreal-shift lower bound. -/
theorem IsSelfAdjoint.abs_im_mul_norm_le_norm_sub_smul
    (hA : IsSelfAdjoint A) (z : ℂ) (x : A.domain) :
    |z.im| * ‖(x : H)‖ ≤ ‖A x - z • (x : H)‖ := by
  have hadj : A.adjoint = A := LinearPMap.isSelfAdjoint_def.mp hA
  have hformal : A.IsFormalAdjoint A := by
    simpa only [hadj] using LinearPMap.adjoint_isFormalAdjoint hA.dense_domain
  exact hformal.abs_im_mul_norm_le_norm_sub_smul z x

/-- A nonreal shift of a self-adjoint operator has trivial kernel on its domain. -/
theorem IsSelfAdjoint.sub_smul_eq_zero_iff
    (hA : IsSelfAdjoint A) {z : ℂ} (hz : z.im ≠ 0) (x : A.domain) :
    A x - z • (x : H) = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have hbound := hA.abs_im_mul_norm_le_norm_sub_smul z x
    rw [hx, norm_zero] at hbound
    have himpos : 0 < |z.im| := abs_pos.mpr hz
    have hnorm : ‖(x : H)‖ = 0 := by nlinarith [norm_nonneg (x : H)]
    exact Subtype.ext (norm_eq_zero.mp hnorm)
  · rintro rfl
    simp

/-- The domain-level nonreal shift of a self-adjoint operator is injective. -/
theorem IsSelfAdjoint.shiftDomainMap_injective
    (hA : IsSelfAdjoint A) {z : ℂ} (hz : z.im ≠ 0) :
    Function.Injective (shiftDomainMap A z) := by
  intro x y hxy
  have hzero : shiftDomainMap A z (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hsub : A (x - y) - z • ((x - y : A.domain) : H) = 0 := by
    simpa only [shiftDomainMap_apply] using hzero
  have hxy0 : x - y = 0 := (hA.sub_smul_eq_zero_iff hz (x - y)).mp hsub
  exact sub_eq_zero.mp hxy0

end

end LinearPMap
