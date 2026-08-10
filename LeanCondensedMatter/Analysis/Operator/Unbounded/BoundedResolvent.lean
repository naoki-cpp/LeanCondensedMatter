import LeanCondensedMatter.Analysis.Operator.Unbounded.SelfAdjointResolvent
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Bounded nonreal resolvents of self-adjoint operators

For a self-adjoint partial operator `A` on a complex Hilbert space and a nonreal scalar `z`, the
previous resolvent infrastructure proves that the domain map `x ↦ A x - z x` is bijective. The
standard lower bound

`|im z| ‖x‖ ≤ ‖A x - z x‖`

then makes its inverse continuous, with norm controlled pointwise by `|im z|⁻¹`. Composing the
domain-valued inverse with the continuous inclusion of the operator domain into the ambient Hilbert
space gives the bounded resolvent `(A - z)⁻¹` used by the later Cayley-transform construction.
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

end

end LinearPMap
