import LeanCondensedMatter.Analysis.ConservationLaw.SymmetricLocalizationAlgebra
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.ChargeDensity

set_option linter.style.header false

/-!
# Fermionic many-body bridge for generalized localized quantities

The representation-independent symmetric-localization realization is owned upstream by
`Analysis.Calculus.SymmetricLocalizationAlgebra` under the root `ConservationLaw` namespace. This
module contains only the fermionic second-quantization bridge:

```text
one-body quantity m
  → localized quantity ρₘ(f)
  → dΓ(ρₘ(f))
```

and the corresponding preservation of the transport/source balance decomposition by `dΓ`.
No local current-density representation is chosen here.
-/

namespace SecondQuantization
namespace Fermionic
namespace Field

attribute [local instance 100] LieRing.ofAssociativeRing

variable {Test : Type*} [AddCommGroup Test] [Module ℂ Test]
variable (𝓗₁ : Type*) [AddCommGroup 𝓗₁] [Module ℂ 𝓗₁]

/-- The total many-body observable associated with a one-particle quantity `m`. -/
noncomputable def oneBodyObservable (m : 𝓗₁ →ₗ[ℂ] 𝓗₁) :
    AlgebraicFock 𝓗₁ →ₗ[ℂ] AlgebraicFock 𝓗₁ :=
  AlgebraicFock.dGamma 𝓗₁ m

/-- Charge-like total observables are scalar multiples of the algebraic number operator. -/
theorem oneBodyObservable_smul_id (q : ℂ) :
    oneBodyObservable 𝓗₁ (q • LinearMap.id) =
      q • AlgebraicFock.totalNumberOperator 𝓗₁ := by
  simpa only [oneBodyObservable, AlgebraicFock.totalNumberOperator,
    AlgebraicFock.dGammaLinear_apply] using
    (AlgebraicFock.dGammaLinear 𝓗₁).map_smul q LinearMap.id

/-- Many-body lift of a generalized localized quantity. -/
noncomputable def manyBodyLocalizedQuantity (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁))
    (m : 𝓗₁ →ₗ[ℂ] 𝓗₁) (f : Test) :
    AlgebraicFock 𝓗₁ →ₗ[ℂ] AlgebraicFock 𝓗₁ :=
  AlgebraicFock.dGamma 𝓗₁ (_root_.ConservationLaw.localizedQuantity 𝓗₁ M m f)

/-- The generalized localized many-body quantity recovers the existing charge-density API for
`m = q I`. -/
theorem manyBodyLocalizedQuantity_smul_id
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁)) (q : ℂ) (f : Test) :
    manyBodyLocalizedQuantity 𝓗₁ M (q • LinearMap.id) f =
      chargeDensity 𝓗₁ q M f := by
  calc
    manyBodyLocalizedQuantity 𝓗₁ M (q • LinearMap.id) f =
        AlgebraicFock.dGamma 𝓗₁ (q • M f) := by
      rw [manyBodyLocalizedQuantity, _root_.ConservationLaw.localizedQuantity_smul_id]
    _ = q • AlgebraicFock.dGamma 𝓗₁ (M f) := by
      simpa only [AlgebraicFock.dGammaLinear_apply] using
        (AlgebraicFock.dGammaLinear 𝓗₁).map_smul q (M f)
    _ = chargeDensity 𝓗₁ q M f := by
      symm
      exact chargeDensity_apply 𝓗₁ q M f

/-- Second quantization preserves the generalized balance decomposition. -/
theorem dGamma_commutator_manyBodyLocalizedQuantity (h : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁)) (m : 𝓗₁ →ₗ[ℂ] 𝓗₁) (f : Test) :
    ⁅AlgebraicFock.dGamma 𝓗₁ h, manyBodyLocalizedQuantity 𝓗₁ M m f⁆ =
      AlgebraicFock.dGamma 𝓗₁ (_root_.ConservationLaw.transportCommutator 𝓗₁ h M m f) +
        AlgebraicFock.dGamma 𝓗₁ (_root_.ConservationLaw.sourceCommutator 𝓗₁ h M m f) := by
  rw [manyBodyLocalizedQuantity, AlgebraicFock.dGamma_lie,
    _root_.ConservationLaw.lie_localizedQuantity]
  simpa only [AlgebraicFock.dGammaLinear_apply] using
    (AlgebraicFock.dGammaLinear 𝓗₁).map_add
      (_root_.ConservationLaw.transportCommutator 𝓗₁ h M m f)
      (_root_.ConservationLaw.sourceCommutator 𝓗₁ h M m f)

/-- A vanishing one-particle commutator gives conservation of the corresponding total many-body
quantity. This is a global statement only; no local-current representation is inferred. -/
theorem oneBodyObservable_commutes_of_commutes (h m : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (hm : ⁅h, m⁆ = 0) :
    ⁅AlgebraicFock.dGamma 𝓗₁ h, oneBodyObservable 𝓗₁ m⁆ = 0 := by
  rw [oneBodyObservable, AlgebraicFock.dGamma_linearCommutator, hm,
    AlgebraicFock.dGamma_zero]

end Field
end Fermionic
end SecondQuantization
