import LeanCondensedMatter.Analysis.Operator.SymmetrizedProduct
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.SecondQuantizationCommutator

set_option linter.style.header false

/-!
# Fermionic many-body bridge for generalized localized quantities

The localized one-body symmetric product is formed before the fermionic `dΓ` lift.
Linearity gives the lifted quantity by composition, and the Lie homomorphism property
preserves the commutator balance. No product-preservation property of `dΓ` is assumed.
-/

namespace SecondQuantization
namespace Fermionic
namespace Field

attribute [local instance 100] LieRing.ofAssociativeRing

variable {Test : Type*} [AddCommGroup Test] [Module ℂ Test]
variable (𝓗₁ : Type*) [AddCommGroup 𝓗₁] [Module ℂ 𝓗₁]

/-- Second quantization preserves the generalized balance decomposition. -/
theorem dGamma_lie_manyBodyLocalizedQuantity
    (h : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁))
    (m : 𝓗₁ →ₗ[ℂ] 𝓗₁) (f : Test) :
    ⁅AlgebraicFock.dGamma 𝓗₁ h,
      AlgebraicFock.dGamma 𝓗₁ (LinearMap.symmetrizedProduct (K := ℂ) (M f) m)⁆ =
      AlgebraicFock.dGamma 𝓗₁ (LinearMap.symmetrizedProduct (K := ℂ) ⁅h, M f⁆ m) +
        AlgebraicFock.dGamma 𝓗₁ (LinearMap.symmetrizedProduct (K := ℂ) (M f) ⁅h, m⁆) := by
  rw [AlgebraicFock.dGamma_lie, LinearMap.lie_symmetrizedProduct]
  simpa only [AlgebraicFock.dGammaLinear_apply] using
    (AlgebraicFock.dGammaLinear 𝓗₁).map_add
      (LinearMap.symmetrizedProduct (K := ℂ) ⁅h, M f⁆ m)
      (LinearMap.symmetrizedProduct (K := ℂ) (M f) ⁅h, m⁆)

end Field
end Fermionic
end SecondQuantization
