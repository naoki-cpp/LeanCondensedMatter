import LeanCondensedMatter.Analysis.Operator.Unbounded.SelfAdjointResolvent
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Tactic.Module
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Abel

set_option linter.style.header false

/-!
# Bounded nonreal resolvents of self-adjoint operators

For a self-adjoint partial operator `A` on a complex Hilbert space and a nonreal scalar `z`, the
previous resolvent infrastructure proves that the domain map `x ↦ A x - z x` is bijective. The
standard lower bound

`|im z| ‖x‖ ≤ ‖A x - z x‖`

then makes its inverse continuous, with norm controlled pointwise by `|im z|⁻¹`. Composing the
domain-valued inverse with the continuous inclusion of the operator domain into the ambient Hilbert
space gives the bounded resolvent `(A - z)⁻¹`. The left and right inverse identities imply the
resolvent identity and pairwise commutation. The adjoint is the resolvent at the conjugate
spectral parameter. The associated Cayley transform `1 + (z - star z) • R(z)` is unitary.
-/

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
  calc
    nonrealResolvent A hA z hz (A x) =
        nonrealResolvent A hA z hz ((A x - z • (x : H)) + z • (x : H)) := by
      congr 1
      module
    _ = nonrealResolvent A hA z hz (A x - z • (x : H)) +
        nonrealResolvent A hA z hz (z • (x : H)) := by
      exact (nonrealResolvent A hA z hz).map_add _ _
    _ = nonrealResolvent A hA z hz (A x - z • (x : H)) +
        z • nonrealResolvent A hA z hz (x : H) := by
      congr 1
      exact (nonrealResolvent A hA z hz).map_smul z (x : H)
    _ = (x : H) + z • nonrealResolvent A hA z hz (x : H) := by
      rw [h]

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
