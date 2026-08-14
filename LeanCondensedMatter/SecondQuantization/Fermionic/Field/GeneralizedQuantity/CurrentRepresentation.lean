import LeanCondensedMatter.Analysis.Calculus.CurrentRepresentation
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.GeneralizedQuantity

set_option linter.style.header false

/-!
# Generalized one-body transport functionals

The representation-independent weak-current abstractions live in
`Analysis.Calculus.CurrentRepresentation` under `ConservationLaw`.  This module contains only the
second-quantized one-particle specialization: the canonical transport commutator is packaged as a
complex-linear functional of localization tests, and charge-like quantities inherit any supplied
differential factorization of the bare localization commutator.
-/

namespace SecondQuantization
namespace Fermionic
namespace Field

variable {Test OneForm : Type*}
variable [AddCommGroup Test] [Module ℂ Test]
variable [AddCommGroup OneForm] [Module ℂ OneForm]
variable (𝓗₁ : Type*) [AddCommGroup 𝓗₁] [Module ℂ 𝓗₁]

/-- The canonical transport term packaged as a linear functional of the localization test object.

This is the linear-map form of `transportCommutator`; downstream models can state precisely that
it factors through a gradient or other differential-like map. -/
noncomputable def transportFunctional
    (h : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁))
    (m : 𝓗₁ →ₗ[ℂ] 𝓗₁) :
    Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁) where
  toFun := transportCommutator 𝓗₁ h M m
  map_add' := by
    intro f g
    apply LinearMap.ext
    intro v
    simp [transportCommutator, symmetrizedProduct, AlgebraicFock.linearCommutator]
    module
  map_smul' := by
    intro c f
    apply LinearMap.ext
    intro v
    simp [transportCommutator, symmetrizedProduct, AlgebraicFock.linearCommutator]
    module

@[simp]
theorem transportFunctional_apply
    (h : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁))
    (m : 𝓗₁ →ₗ[ℂ] 𝓗₁) (f : Test) :
    transportFunctional 𝓗₁ h M m f = transportCommutator 𝓗₁ h M m f :=
  rfl

/-- The bare localization commutator `f ↦ [h, M(f)]`, packaged linearly. Charge transport is a
scalar multiple of this functional. -/
noncomputable def localizationCommutatorFunctional
    (h : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁)) :
    Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁) where
  toFun := fun f => AlgebraicFock.linearCommutator h (M f)
  map_add' := by
    intro f g
    apply LinearMap.ext
    intro v
    simp [AlgebraicFock.linearCommutator]
    module
  map_smul' := by
    intro c f
    apply LinearMap.ext
    intro v
    simp [AlgebraicFock.linearCommutator]
    module

@[simp]
theorem localizationCommutatorFunctional_apply
    (h : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁)) (f : Test) :
    localizationCommutatorFunctional 𝓗₁ h M f =
      AlgebraicFock.linearCommutator h (M f) :=
  rfl

/-- For `m = q I`, the generalized transport functional is exactly `q` times the bare
localization commutator functional. -/
theorem transportFunctional_smul_id
    (h : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁)) (q : ℂ) :
    transportFunctional 𝓗₁ h M (q • LinearMap.id) =
      q • localizationCommutatorFunctional 𝓗₁ h M := by
  apply LinearMap.ext
  intro f
  simp

/-- Any differential factorization of the bare localization commutator induces the corresponding
charge-current factorization for `m = q I`. -/
theorem factorsThroughDifferential_transport_smul_id
    (h : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁))
    (d : Test →ₗ[ℂ] OneForm)
    (J : OneForm →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁))
    (q : ℂ)
    (hJ : ConservationLaw.FactorsThroughDifferential d
      (localizationCommutatorFunctional 𝓗₁ h M) J) :
    ConservationLaw.FactorsThroughDifferential d
      (transportFunctional 𝓗₁ h M (q • LinearMap.id)) (q • J) := by
  rw [transportFunctional_smul_id]
  exact ConservationLaw.FactorsThroughDifferential.smul hJ q

end Field
end Fermionic
end SecondQuantization
