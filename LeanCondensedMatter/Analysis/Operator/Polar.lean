import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs

set_option linter.style.header false

/-!
# Polar factor for bounded operators

This module provides the bounded partial-isometry factor needed from polar decomposition. For a
bounded endomorphism `T`, it constructs a contraction `U` with
`U |T| = T` and `U† T = |T|`.
-/

noncomputable section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem norm_cfcAbs_apply_eq (T : H →L[ℂ] H) (x : H) :
    ‖CFC.abs T x‖ = ‖T x‖ := by
  have h : (ContinuousLinearMap.adjoint (CFC.abs T)).comp (CFC.abs T) =
      (ContinuousLinearMap.adjoint T).comp T := by
    change ContinuousLinearMap.adjoint (CFC.abs T) * CFC.abs T =
      ContinuousLinearMap.adjoint T * T
    rw [(CFC.abs_nonneg T).isSelfAdjoint.adjoint_eq, CFC.abs_mul_abs,
      ContinuousLinearMap.star_eq_adjoint]
  rw [apply_norm_eq_sqrt_inner_adjoint_left (CFC.abs T),
    apply_norm_eq_sqrt_inner_adjoint_left T, h]

/-- A bounded operator has a contractive left polar factor `U` satisfying
`U |T| = T` and `U† T = |T|`. -/
theorem exists_leftPolarFactor (T : H →L[ℂ] H) :
    ∃ U : H →L[ℂ] H,
      U * CFC.abs T = T ∧
      ContinuousLinearMap.adjoint U * T = CFC.abs T ∧
      ‖U‖ ≤ 1 := by
  let A : H →L[ℂ] H := CFC.abs T
  let R : Submodule ℂ H := LinearMap.range A.toLinearMap
  let C : Submodule ℂ H := R.topologicalClosure
  let j : R →ₗ[ℂ] C := Submodule.inclusion R.le_topologicalClosure
  have hAxC (x : H) : A x ∈ C :=
    R.le_topologicalClosure (LinearMap.mem_range_self A.toLinearMap x)
  have hj_dense : DenseRange j := by
    change DenseRange (Set.inclusion (show (R : Set H) ⊆ (C : Set H) from R.le_topologicalClosure))
    rw [denseRange_inclusion_iff]
    simpa [C, Submodule.topologicalClosure_coe]
  have hbound : ∃ c : ℝ, ∀ x : H, ‖T x‖ ≤ c * ‖A x‖ := by
    refine ⟨1, fun x => ?_⟩
    rw [one_mul, norm_cfcAbs_apply_eq]
  let f : R →L[ℂ] H := T.toLinearMap.compLeftInverse A.toLinearMap
  have hf_norm (y : R) : ‖f y‖ = ‖j y‖ := by
    obtain ⟨x, hx⟩ := y.2
    have hf_apply : f y = T x := by
      simpa [f] using
        LinearMap.compLeftInverse_apply_of_bdd T.toLinearMap A.toLinearMap hbound x y.1 hx
    calc
      ‖f y‖ = ‖T x‖ := by rw [hf_apply]
      _ = ‖A x‖ := (norm_cfcAbs_apply_eq T x).symm
      _ = ‖(y : H)‖ := congrArg norm hx
      _ = ‖j y‖ := rfl
  letI : CompleteSpace C := R.isClosed_topologicalClosure.completeSpace_coe
  let V : C →ₗᵢ[ℂ] H := f.toLinearMap.extendOfIsometry hj_dense hf_norm
  let U : H →L[ℂ] H := V.toContinuousLinearMap.comp C.orthogonalProjectionOnto
  have hleft : U * A = T := by
    apply ContinuousLinearMap.ext
    intro x
    rw [mul_apply_eq_comp]
    change V (C.orthogonalProjectionOnto (A x)) = T x
    let y : R := ⟨A x, LinearMap.mem_range_self A.toLinearMap x⟩
    rw [show C.orthogonalProjectionOnto (A x) = (⟨A x, hAxC x⟩ : C) from
      C.orthogonalProjectionOnto_mem_subspace_eq_self ⟨A x, hAxC x⟩]
    change V (j y) = T x
    rw [LinearMap.extendOfIsometry_eq f.toLinearMap hj_dense hf_norm y]
    simpa [f, y] using
      LinearMap.compLeftInverse_apply_of_bdd T.toLinearMap A.toLinearMap hbound x (A x) rfl
  have hUU : ContinuousLinearMap.adjoint U * U = C.starProjection := by
    change
      (ContinuousLinearMap.adjoint (V.toContinuousLinearMap.comp C.orthogonalProjectionOnto)).comp
          (V.toContinuousLinearMap.comp C.orthogonalProjectionOnto) =
        C.subtypeL.comp C.orthogonalProjectionOnto
    rw [ContinuousLinearMap.adjoint_comp, Submodule.adjoint_orthogonalProjectionOnto,
      ← ContinuousLinearMap.comp_assoc]
    rw [ContinuousLinearMap.comp_assoc C.subtypeL
      (ContinuousLinearMap.adjoint V.toContinuousLinearMap) V.toContinuousLinearMap]
    rw [LinearIsometry.adjoint_comp_self V]
    apply ContinuousLinearMap.ext
    intro x
    rfl
  have hright : ContinuousLinearMap.adjoint U * T = A := by
    rw [← hleft, ← mul_assoc, hUU]
    apply ContinuousLinearMap.ext
    intro x
    rw [mul_apply_eq_comp]
    exact C.starProjection_eq_self_iff.mpr (hAxC x)
  have hcontract : ‖U‖ ≤ 1 := by
    refine (V.toContinuousLinearMap.opNorm_comp_le C.orthogonalProjectionOnto).trans ?_
    simpa only [one_mul] using
      mul_le_mul V.norm_toContinuousLinearMap_le C.orthogonalProjectionOnto_norm_le
        (norm_nonneg _) zero_le_one
  exact ⟨U, hleft, hright, hcontract⟩

end ContinuousLinearMap
