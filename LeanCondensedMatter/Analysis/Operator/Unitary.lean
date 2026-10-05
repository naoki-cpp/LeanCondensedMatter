import LeanCondensedMatter.Analysis.Operator.AdjointConjugation
import LeanCondensedMatter.Analysis.Operator.Spectral.EigenvectorFamily
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option linter.style.header false

/-!
# Unitary properties of adjoint conjugation

This module owns dimension-independent facts about `adjointConjugate` that require the conjugating
operator to satisfy the two adjoint-inverse identities. It does not depend on trace-class
infrastructure.
-/

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ContinuousLinearMap

/-- Package the two-sided adjoint inverse laws as Mathlib's unitary subtype. -/
def unitaryOfAdjointInverse (U : H →L[ℂ] H)
    (hleft : star U * U = 1) (hright : U * star U = 1) :
    unitary (H →L[ℂ] H) :=
  ⟨U, Unitary.mem_iff.mpr ⟨hleft, hright⟩⟩

/-- Unitary conjugation maps each eigenspace to the corresponding eigenspace with the same
eigenvalue. -/
theorem eigenspace_adjointConjugate (U T : H →L[ℂ] H)
    (hleft : star U * U = 1) (hright : U * star U = 1) (μ : ℂ) :
    Module.End.eigenspace ((adjointConjugate U T : H →L[ℂ] H) : H →ₗ[ℂ] H) μ =
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
theorem finrank_eigenspace_adjointConjugate (U T : H →L[ℂ] H)
    (hleft : star U * U = 1) (hright : U * star U = 1) (μ : ℂ) :
    Module.finrank ℂ
        (Module.End.eigenspace ((adjointConjugate U T : H →L[ℂ] H) : H →ₗ[ℂ] H) μ) =
      Module.finrank ℂ (Module.End.eigenspace (T : H →ₗ[ℂ] H) μ) := by
  rw [eigenspace_adjointConjugate U T hleft hright μ]
  exact (Unitary.linearIsometryEquiv
    (unitaryOfAdjointInverse U hleft hright)).toLinearEquiv.finrank_map_eq _

end ContinuousLinearMap
