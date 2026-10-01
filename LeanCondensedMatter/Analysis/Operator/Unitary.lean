import LeanCondensedMatter.Analysis.Operator.Spectral.EigenvectorFamily
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option linter.style.header false

/-!
# Unitary conjugation of bounded operators

This module owns dimension-independent operator facts for conjugation by bounded unitary
representatives.  It does not depend on spectral trace-class infrastructure.

The hypotheses are stated as the two operator inverse identities, so the results are reusable
independently of any particular unitary bundling.
-/

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ContinuousLinearMap

/-- Package the two-sided adjoint inverse laws as Mathlib's unitary subtype. -/
def unitaryOfAdjointInverse (U : H →L[ℂ] H)
    (hleft : star U * U = 1) (hright : U * star U = 1) :
    unitary (H →L[ℂ] H) :=
  ⟨U, Unitary.mem_iff.mpr ⟨hleft, hright⟩⟩

/-- Conjugation of an operator by a unitary representative. -/
noncomputable def unitaryConjugate (U T : H →L[ℂ] H) : H →L[ℂ] H :=
  U * T * star U

/-- Conjugation transports a rank-one operator by applying the conjugating operator to both
vectors. -/
theorem unitaryConjugate_rankOne (U : H →L[ℂ] H) (x y : H) :
    unitaryConjugate U (InnerProductSpace.rankOne ℂ x y) =
      InnerProductSpace.rankOne ℂ (U x) (U y) := by
  ext z
  simp only [unitaryConjugate, mul_apply_eq_comp, InnerProductSpace.rankOne_apply, map_smul,
    ContinuousLinearMap.star_eq_adjoint]
  exact congrArg (fun c : ℂ => c • U x)
    (ContinuousLinearMap.adjoint_inner_right U y z)

/-- Unitary conjugation maps each eigenspace to the corresponding eigenspace with the same
eigenvalue. -/
theorem eigenspace_unitaryConjugate (U T : H →L[ℂ] H)
    (hleft : star U * U = 1) (hright : U * star U = 1) (μ : ℂ) :
    Module.End.eigenspace ((unitaryConjugate U T : H →L[ℂ] H) : H →ₗ[ℂ] H) μ =
      Submodule.map
        (Unitary.linearIsometryEquiv (unitaryOfAdjointInverse U hleft hright)).toLinearEquiv.toLinearMap
        (Module.End.eigenspace (T : H →ₗ[ℂ] H) μ) := by
  ext x
  constructor
  · intro hx
    rw [Submodule.mem_map]
    refine ⟨star U x, ?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff] at hx ⊢
      change U (T ((star U) x)) = μ • x at hx
      have h := congrArg (fun y : H => (star U) y) hx
      have hcancel : (star U) (U (T ((star U) x))) = T ((star U) x) := by
        have h' := congrArg (fun A : H →L[ℂ] H => A (T ((star U) x))) hleft
        simpa [mul_apply_eq_comp] using h'
      simpa [hcancel, map_smul] using h
    · change U ((star U) x) = x
      have h := congrArg (fun A : H →L[ℂ] H => A x) hright
      simpa [mul_apply_eq_comp] using h
  · intro hx
    rw [Submodule.mem_map] at hx
    rcases hx with ⟨y, hy, rfl⟩
    rw [Module.End.mem_eigenspace_iff] at hy ⊢
    change U (T ((star U) (U y))) = μ • U y
    have hcancel : (star U) (U y) = y := by
      have h := congrArg (fun A : H →L[ℂ] H => A y) hleft
      simpa [mul_apply_eq_comp] using h
    rw [hcancel]
    simpa using congrArg (fun z : H => U z) hy

/-- Corresponding eigenspaces have the same finite dimension under unitary conjugation. -/
theorem finrank_eigenspace_unitaryConjugate (U T : H →L[ℂ] H)
    (hleft : star U * U = 1) (hright : U * star U = 1) (μ : ℂ) :
    Module.finrank ℂ
        (Module.End.eigenspace ((unitaryConjugate U T : H →L[ℂ] H) : H →ₗ[ℂ] H) μ) =
      Module.finrank ℂ (Module.End.eigenspace (T : H →ₗ[ℂ] H) μ) := by
  rw [eigenspace_unitaryConjugate U T hleft hright μ]
  exact (Unitary.linearIsometryEquiv
    (unitaryOfAdjointInverse U hleft hright)).toLinearEquiv.finrank_map_eq _

end ContinuousLinearMap
