import LeanCondensedMatter.Analysis.ConservationLaw.SymmetricLocalizationAlgebra
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.SecondQuantizationCommutator

set_option linter.style.header false

/-!
# Fermionic many-body bridge for generalized localized quantities

The representation-independent symmetric-localization realization is owned upstream by
`Analysis.ConservationLaw.SymmetricLocalizationAlgebra` under the root `ConservationLaw` namespace.
This module contains only the fermionic second-quantization bridge:

```text
one-body localized quantity functional
  → dΓ
  → many-body localized quantity functional
```

and the corresponding preservation of the transport/source balance decomposition by `dΓ`.
No local current-density representation or charge specialization is chosen here.
-/

namespace SecondQuantization
namespace Fermionic
namespace Field

attribute [local instance 100] LieRing.ofAssociativeRing

variable {Test : Type*} [AddCommGroup Test] [Module ℂ Test]
variable (𝓗₁ : Type*) [AddCommGroup 𝓗₁] [Module ℂ 𝓗₁]

/-- Many-body lift of a generalized localized quantity, packaged linearly in the test object. -/
noncomputable def manyBodyLocalizedQuantity
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁))
    (m : 𝓗₁ →ₗ[ℂ] 𝓗₁) :
    Test →ₗ[ℂ] (AlgebraicFock 𝓗₁ →ₗ[ℂ] AlgebraicFock 𝓗₁) :=
  (AlgebraicFock.dGammaLinear 𝓗₁).comp
    (_root_.ConservationLaw.localizedQuantityFunctional 𝓗₁ M m)

@[simp]
theorem manyBodyLocalizedQuantity_apply
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁))
    (m : 𝓗₁ →ₗ[ℂ] 𝓗₁) (f : Test) :
    manyBodyLocalizedQuantity 𝓗₁ M m f =
      AlgebraicFock.dGamma 𝓗₁ (_root_.ConservationLaw.localizedQuantity 𝓗₁ M m f) :=
  rfl

/-- Second quantization preserves the generalized balance decomposition. -/
theorem dGamma_lie_manyBodyLocalizedQuantity
    (h : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁))
    (m : 𝓗₁ →ₗ[ℂ] 𝓗₁) (f : Test) :
    ⁅AlgebraicFock.dGamma 𝓗₁ h, manyBodyLocalizedQuantity 𝓗₁ M m f⁆ =
      AlgebraicFock.dGamma 𝓗₁ (_root_.ConservationLaw.transportCommutator 𝓗₁ h M m f) +
        AlgebraicFock.dGamma 𝓗₁ (_root_.ConservationLaw.sourceCommutator 𝓗₁ h M m f) := by
  rw [manyBodyLocalizedQuantity_apply, AlgebraicFock.dGamma_lie,
    _root_.ConservationLaw.lie_localizedQuantity]
  simpa only [AlgebraicFock.dGammaLinear_apply] using
    (AlgebraicFock.dGammaLinear 𝓗₁).map_add
      (_root_.ConservationLaw.transportCommutator 𝓗₁ h M m f)
      (_root_.ConservationLaw.sourceCommutator 𝓗₁ h M m f)

end Field
end Fermionic
end SecondQuantization
