module

public import LeanCondensedMatter.Analysis.Operator.AdjointConjugation
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank

public section

set_option linter.style.header false

/-!
# Unitary properties of adjoint conjugation

This module owns dimension-independent facts about `adjointConjugate` that require the conjugating
operator to satisfy the two adjoint-inverse identities. It does not depend on trace-class
infrastructure.
-/

noncomputable section

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]

namespace ContinuousLinearMap

/-- Package the two-sided adjoint inverse laws as Mathlib's unitary subtype. -/
@[expose] def unitaryOfAdjointInverse (U : H →L[𝕜] H)
    (hleft : star U * U = 1) (hright : U * star U = 1) :
    unitary (H →L[𝕜] H) :=
  ⟨U, Unitary.mem_iff.mpr ⟨hleft, hright⟩⟩

/-- Unitary conjugation maps each eigenspace to the corresponding eigenspace with the same
eigenvalue. -/
theorem eigenspace_adjointConjugate (U T : H →L[𝕜] H)
    (hleft : star U * U = 1) (hright : U * star U = 1) (μ : 𝕜) :
    Module.End.eigenspace ((adjointConjugate U T : H →L[𝕜] H) : H →ₗ[𝕜] H) μ =
      Submodule.map
        (Unitary.linearIsometryEquiv (unitaryOfAdjointInverse U hleft hright)).toLinearEquiv.toLinearMap
        (Module.End.eigenspace (T : H →ₗ[𝕜] H) μ) := by
  let e : H ≃ₗ[𝕜] H :=
    (Unitary.linearIsometryEquiv (unitaryOfAdjointInverse U hleft hright)).toLinearEquiv
  change _ = Submodule.map e.toLinearMap _
  ext x
  rw [Submodule.mem_map_equiv, Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff]
  change e (T (e.symm x)) = μ • x ↔ T (e.symm x) = μ • e.symm x
  calc
    e (T (e.symm x)) = μ • x ↔ e (T (e.symm x)) = e (μ • e.symm x) := by
      rw [map_smul, e.apply_symm_apply]
    _ ↔ T (e.symm x) = μ • e.symm x := e.injective.eq_iff

/-- Corresponding eigenspaces have the same finite dimension under unitary conjugation. -/
theorem finrank_eigenspace_adjointConjugate (U T : H →L[𝕜] H)
    (hleft : star U * U = 1) (hright : U * star U = 1) (μ : 𝕜) :
    Module.finrank 𝕜
        (Module.End.eigenspace ((adjointConjugate U T : H →L[𝕜] H) : H →ₗ[𝕜] H) μ) =
      Module.finrank 𝕜 (Module.End.eigenspace (T : H →ₗ[𝕜] H) μ) := by
  rw [eigenspace_adjointConjugate U T hleft hright μ]
  exact (Unitary.linearIsometryEquiv
    (unitaryOfAdjointInverse U hleft hright)).toLinearEquiv.finrank_map_eq _

end ContinuousLinearMap
