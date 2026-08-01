import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonExpansion
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.InteractionPicture

set_option linter.style.header false

/-!
# Temporary fermionic Dyson specializations

The authoritative Dyson construction is `SecondQuantization.Common.dysonCoeff`. This file retains
only the fermionic specializations that are still referenced by the current diagrammatic proof
stack. Unused forwarding declarations are intentionally removed; the remaining callers will be
migrated to the Common API before this module is deleted.
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

noncomputable abbrev dysonCoeff (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :=
  Common.dysonCoeff (fermionEnergy ε) V

omit [LinearOrder Mode] in
theorem dysonCoeff_zero (ε : Mode → ℝ) (V : FockSpaceFermionic Mode →ₗ[ℂ]
    FockSpaceFermionic Mode) (τ : ℝ) : dysonCoeff ε V 0 τ = LinearMap.id :=
  Common.dysonCoeff_zero (fermionEnergy ε) V τ

omit [LinearOrder Mode] in
theorem dysonCoeff_succ (ε : Mode → ℝ) (V : FockSpaceFermionic Mode →ₗ[ℂ]
    FockSpaceFermionic Mode) (n : ℕ) (τ : ℝ) : dysonCoeff ε V (n + 1) τ =
    - Common.operatorIntervalIntegral
      (fun σ => (interactionPicture ε V σ).comp (dysonCoeff ε V n σ)) 0 τ :=
  Common.dysonCoeff_succ (fermionEnergy ε) V n τ

omit [LinearOrder Mode] in
theorem continuous_matrixCoeff_dysonCoeff (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (n : ℕ) :
    ∀ m n' : FermionOccupation Mode,
      Continuous (fun τ : ℝ => Common.matrixCoeff (dysonCoeff ε V n τ) m n') :=
  Common.continuous_matrixCoeff_dysonCoeff (fermionEnergy ε) V n

end SecondQuantization
