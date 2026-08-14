import LeanCondensedMatter.Analysis.Calculus.CurrentRepresentation
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.GeneralizedQuantity

set_option linter.style.header false

/-!
# Generalized one-body transport functionals

The representation-independent weak-current abstractions live in
`Analysis.Calculus.CurrentRepresentation` under `ConservationLaw`. This module contains only the
second-quantized one-particle specialization: the canonical transport commutator is packaged as a
complex-linear functional of localization tests.

Whenever the bare localization commutator factors through a differential-like map, the transport
functional for an arbitrary one-body quantity `m` inherits that factorization by postcomposing the
bare flux functional with `A ↦ 1/2 {A, m}`. This is deliberately only a differential factorization:
it does not assert the existence of a zeroth-order local vector-current density.
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

/-- Symmetrization with a fixed one-body quantity is linear in the transport operator.

This is the algebraic operation taking a bare localization-transfer operator `A` to the generalized
quantity transfer `1/2 {A, m}`. -/
noncomputable def symmetrizedProductRightLinear
    (m : 𝓗₁ →ₗ[ℂ] 𝓗₁) :
    (𝓗₁ →ₗ[ℂ] 𝓗₁) →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁) where
  toFun := fun A => symmetrizedProduct A m
  map_add' := by
    intro A B
    apply LinearMap.ext
    intro v
    simp [symmetrizedProduct]
    module
  map_smul' := by
    intro c A
    apply LinearMap.ext
    intro v
    simp [symmetrizedProduct]
    module

@[simp]
theorem symmetrizedProductRightLinear_apply
    (m A : 𝓗₁ →ₗ[ℂ] 𝓗₁) :
    symmetrizedProductRightLinear 𝓗₁ m A = symmetrizedProduct A m :=
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

/-- The generalized transport functional is obtained by postcomposing the bare localization
commutator with symmetrization by `m`.

This identity is representation-independent and does not require `m` to commute with localization. -/
theorem transportFunctional_eq_symmetrizedProductRight_comp
    (h : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁))
    (m : 𝓗₁ →ₗ[ℂ] 𝓗₁) :
    transportFunctional 𝓗₁ h M m =
      (symmetrizedProductRightLinear 𝓗₁ m).comp
        (localizationCommutatorFunctional 𝓗₁ h M) := by
  apply LinearMap.ext
  intro f
  rfl

/-- Any differential factorization of the bare localization commutator induces a differential
factorization of the canonical transport functional for an arbitrary one-body quantity `m`.

The induced flux functional is `α ↦ 1/2 {J(α), m}`. No zeroth-order/local-current-density claim is
made here; that requires additional compatibility and locality hypotheses. -/
theorem factorsThroughDifferential_transport
    (h : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁))
    (m : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (d : Test →ₗ[ℂ] OneForm)
    (J : OneForm →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁))
    (hJ : ConservationLaw.FactorsThroughDifferential d
      (localizationCommutatorFunctional 𝓗₁ h M) J) :
    ConservationLaw.FactorsThroughDifferential d
      (transportFunctional 𝓗₁ h M m)
      ((symmetrizedProductRightLinear 𝓗₁ m).comp J) := by
  rw [transportFunctional_eq_symmetrizedProductRight_comp]
  exact ConservationLaw.FactorsThroughDifferential.postcomp hJ
    (symmetrizedProductRightLinear 𝓗₁ m)

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
