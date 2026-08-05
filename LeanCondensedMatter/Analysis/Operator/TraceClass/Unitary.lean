import LeanCondensedMatter.Analysis.Operator.TraceClass.Bundled
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option linter.style.header false

/-!
# Unitary conjugation of spectral-trace-class operators

This module provides the algebraic spectral bridge needed to transport density operators under
bounded unitary dynamics.  The hypotheses are stated as the two operator inverse identities, so the
results are reusable independently of any particular unitary bundling.
-/

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ContinuousLinearMap

/-- The linear equivalence implemented by an operator whose adjoint is a two-sided inverse. -/
noncomputable def unitaryLinearEquiv (U : H →L[ℂ] H)
    (hleft : star U * U = 1) (hright : U * star U = 1) : H ≃ₗ[ℂ] H where
  toFun := U
  invFun := star U
  left_inv := fun x => by
    have h := congrArg (fun A : H →L[ℂ] H => A x) hleft
    simpa [mul_apply_eq_comp] using h
  right_inv := fun x => by
    have h := congrArg (fun A : H →L[ℂ] H => A x) hright
    simpa [mul_apply_eq_comp] using h
  map_add' := U.map_add
  map_smul' := U.map_smul

/-- Conjugation of an operator by a unitary representative. -/
noncomputable def unitaryConjugate (U T : H →L[ℂ] H) : H →L[ℂ] H :=
  U * T * star U

/-- Unitary conjugation maps each eigenspace to the corresponding eigenspace with the same
eigenvalue. -/
theorem eigenspace_unitaryConjugate (U T : H →L[ℂ] H)
    (hleft : star U * U = 1) (hright : U * star U = 1) (μ : ℂ) :
    Module.End.eigenspace ((unitaryConjugate U T : H →L[ℂ] H) : H →ₗ[ℂ] H) μ =
      Submodule.map (unitaryLinearEquiv U hleft hright).toLinearMap
        (Module.End.eigenspace (T : H →ₗ[ℂ] H) μ) := by
  ext x
  constructor
  · intro hx
    rw [Submodule.mem_map]
    refine ⟨star U x, ?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff] at hx ⊢
      have h := congrArg (fun y : H => star U y) hx
      have hcancel : star U (U (T (star U x))) = T (star U x) := by
        have h' := congrArg (fun A : H →L[ℂ] H => A (T (star U x))) hleft
        simpa [mul_apply_eq_comp] using h'
      rw [unitaryConjugate, mul_apply_eq_comp] at hx
      rw [hcancel, map_smul] at h
      exact h
    · have h := congrArg (fun A : H →L[ℂ] H => A x) hright
      simpa [mul_apply_eq_comp] using h
  · intro hx
    rw [Submodule.mem_map] at hx
    rcases hx with ⟨y, hy, rfl⟩
    rw [Module.End.mem_eigenspace_iff] at hy ⊢
    have hcancel : star U (U y) = y := by
      have h := congrArg (fun A : H →L[ℂ] H => A y) hleft
      simpa [mul_apply_eq_comp] using h
    rw [unitaryConjugate, mul_apply_eq_comp, hcancel, hy, map_smul]

/-- Corresponding eigenspaces have the same finite dimension under unitary conjugation. -/
theorem finrank_eigenspace_unitaryConjugate (U T : H →L[ℂ] H)
    (hleft : star U * U = 1) (hright : U * star U = 1) (μ : ℂ) :
    Module.finrank ℂ
        (Module.End.eigenspace ((unitaryConjugate U T : H →L[ℂ] H) : H →ₗ[ℂ] H) μ) =
      Module.finrank ℂ (Module.End.eigenspace (T : H →ₗ[ℂ] H) μ) := by
  rw [eigenspace_unitaryConjugate U T hleft hright μ]
  exact (unitaryLinearEquiv U hleft hright).finrank_map_eq _

end ContinuousLinearMap
