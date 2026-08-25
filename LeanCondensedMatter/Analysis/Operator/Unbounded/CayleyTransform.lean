import LeanCondensedMatter.Analysis.Operator.Unbounded.BoundedResolvent
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Cayley transform of an unbounded self-adjoint operator

The bounded nonreal resolvent lets us form the Cayley transform of a self-adjoint partial operator
without an unbounded functional calculus. For nonreal `z`, define

`C_z = 1 + (z - star z) (A - z)⁻¹`.

On a vector `y`, if `u = (A - z)⁻¹ y`, then `C_z y = (A - star z) u`. The resolvent adjoint
identity gives `R_z† = R_(star z)`, and consequently `C_z† = C_(star z)`. The two Cayley
transforms are mutual inverses, so `C_z` is unitary.

The Cayley transform supplies the unitary resolvent transform used by the bounded rational
approximation layer of the Stone-theorem construction.
-/

namespace LinearPMap

noncomputable section

open Complex
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem star_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) : (star z).im ≠ 0 := by
  simpa using neg_ne_zero.mpr hz

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
