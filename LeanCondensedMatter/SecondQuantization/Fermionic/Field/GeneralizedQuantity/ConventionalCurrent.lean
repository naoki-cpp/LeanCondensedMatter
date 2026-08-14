import LeanCondensedMatter.SecondQuantization.Fermionic.Field.GeneralizedQuantity.CurrentRepresentation
import Mathlib.Tactic.Module

set_option linter.style.header false

/-!
# Conventional current as a specialization of generalized transport

The primitive generalized transport API is expressed in terms of the commutator `[h, M f]`.
For physical currents one instead uses the Heisenberg derivation

```text
δₕ(A) = (i / ℏ) [h, A].
```

This module adds that scalar wrapper and proves the algebraic specialization behind the usual
current formula.  Suppose a differential-like test `d f` is localized by `N`, and the Heisenberg
motion of localization has the first-order form

```text
δₕ(M f) = 1/2 {N (d f), v}.
```

If `N α` commutes with the transported one-body quantity `m`, then the generalized transport
functional has the zeroth-order operator-local pairing

```text
Φₘ(f) = 1/2 {N (d f), jᵐ},

jᵐ = 1/2 {v, m}.
```

Thus `jᵐ` is a genuine `LocalCurrentDensityRepresentation` relative to the supplied localization
pairing.  The commutation hypothesis is explicit: this theorem is intended for internal quantities
such as charge or spin, and must not be applied automatically to differential/nonlocal quantities
such as continuum orbital angular momentum.
-/

namespace SecondQuantization
namespace Fermionic
namespace Field

variable {Test OneForm : Type*}
variable [AddCommGroup Test] [Module ℂ Test]
variable [AddCommGroup OneForm] [Module ℂ OneForm]
variable (𝓗₁ : Type*) [AddCommGroup 𝓗₁] [Module ℂ 𝓗₁]

/-- Scalar converting a commutator with the Hamiltonian into the Heisenberg derivative. -/
noncomputable def heisenbergScale (ℏ : ℝ) : ℂ :=
  Complex.I / (ℏ : ℂ)

/-- The localization commutator functional scaled to the physical Heisenberg derivative. -/
noncomputable def heisenbergLocalizationFunctional
    (ℏ : ℝ) (h : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁)) :
    Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁) :=
  heisenbergScale ℏ • localizationCommutatorFunctional 𝓗₁ h M

/-- The generalized transport functional scaled to the physical Heisenberg derivative. -/
noncomputable def heisenbergTransportFunctional
    (ℏ : ℝ) (h : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁))
    (m : 𝓗₁ →ₗ[ℂ] 𝓗₁) :
    Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁) :=
  heisenbergScale ℏ • transportFunctional 𝓗₁ h M m

@[simp]
theorem heisenbergLocalizationFunctional_apply
    (ℏ : ℝ) (h : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁)) (f : Test) :
    heisenbergLocalizationFunctional 𝓗₁ ℏ h M f =
      heisenbergScale ℏ • AlgebraicFock.linearCommutator h (M f) :=
  rfl

@[simp]
theorem heisenbergTransportFunctional_apply
    (ℏ : ℝ) (h : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁))
    (m : 𝓗₁ →ₗ[ℂ] 𝓗₁) (f : Test) :
    heisenbergTransportFunctional 𝓗₁ ℏ h M m f =
      heisenbergScale ℏ • transportCommutator 𝓗₁ h M m f :=
  rfl

/-- Heisenberg scaling commutes with the fixed-`m` symmetrization that builds generalized
transport from bare localization transport. -/
theorem heisenbergTransportFunctional_eq_symmetrizedProductRight_comp
    (ℏ : ℝ) (h : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁))
    (m : 𝓗₁ →ₗ[ℂ] 𝓗₁) :
    heisenbergTransportFunctional 𝓗₁ ℏ h M m =
      (symmetrizedProductRightLinear 𝓗₁ m).comp
        (heisenbergLocalizationFunctional 𝓗₁ ℏ h M) := by
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro x
  simp [heisenbergTransportFunctional, heisenbergLocalizationFunctional,
    heisenbergScale, transportFunctional, transportCommutator,
    localizationCommutatorFunctional, symmetrizedProductRightLinear, symmetrizedProduct]
  module

/-- The conventional one-body current operator `jᵐ = 1/2 {v, m}`. -/
noncomputable def conventionalCurrent
    (velocity m : 𝓗₁ →ₗ[ℂ] 𝓗₁) : 𝓗₁ →ₗ[ℂ] 𝓗₁ :=
  symmetrizedProduct velocity m

@[simp]
theorem conventionalCurrent_smul_id
    (velocity : 𝓗₁ →ₗ[ℂ] 𝓗₁) (q : ℂ) :
    conventionalCurrent 𝓗₁ velocity (q • LinearMap.id) = q • velocity := by
  exact symmetrizedProduct_smul_id velocity q

@[simp]
theorem conventionalCurrent_id
    (velocity : 𝓗₁ →ₗ[ℂ] 𝓗₁) :
    conventionalCurrent 𝓗₁ velocity LinearMap.id = velocity := by
  simpa using conventionalCurrent_smul_id 𝓗₁ velocity (1 : ℂ)

/-- Reassociation identity behind the conventional-current formula.

If the localization operator commutes with `m`, then

`1/2 {1/2 {localizer, velocity}, m} = 1/2 {localizer, 1/2 {velocity, m}}`.
-/
theorem symmetrizedProduct_nested_eq_of_commutes
    (localizer velocity m : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (hcomm : AlgebraicFock.linearCommutator localizer m = 0) :
    symmetrizedProduct (symmetrizedProduct localizer velocity) m =
      symmetrizedProduct localizer (symmetrizedProduct velocity m) := by
  apply LinearMap.ext
  intro x
  have hlocalizer (y : 𝓗₁) : localizer (m y) = m (localizer y) := by
    have h := congrArg (fun T : 𝓗₁ →ₗ[ℂ] 𝓗₁ => T y) hcomm
    have hzero : localizer (m y) - m (localizer y) = 0 := by
      simpa [AlgebraicFock.linearCommutator] using h
    exact sub_eq_zero.mp hzero
  simp [symmetrizedProduct, hlocalizer]
  module

/-- A one-form-like test is paired with a one-body current operator by symmetric localization,
`(j, α) ↦ 1/2 {N α, j}`.

This pairing is zeroth-order relative to the supplied map `N`: it does not differentiate `α`.
Concrete continuum models may further realize `N α` as multiplication by the test 1-form. -/
noncomputable def operatorLocalCurrentPairing
    (N : OneForm →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁)) :
    ConservationLaw.LocalCurrentPairing
      (𝕜 := ℂ)
      (OneForm := OneForm)
      (Obs := 𝓗₁ →ₗ[ℂ] 𝓗₁)
      (CurrentDensity := 𝓗₁ →ₗ[ℂ] 𝓗₁) where
  toFun := fun current => (symmetrizedProductRightLinear 𝓗₁ current).comp N
  map_add' := by
    intro j₁ j₂
    apply LinearMap.ext
    intro α
    apply LinearMap.ext
    intro x
    simp [symmetrizedProductRightLinear, symmetrizedProduct]
    module
  map_smul' := by
    intro c j
    apply LinearMap.ext
    intro α
    apply LinearMap.ext
    intro x
    simp [symmetrizedProductRightLinear, symmetrizedProduct]
    module

@[simp]
theorem operatorLocalCurrentPairing_apply
    (N : OneForm →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁))
    (current : 𝓗₁ →ₗ[ℂ] 𝓗₁) (α : OneForm) :
    operatorLocalCurrentPairing 𝓗₁ N current α =
      symmetrizedProduct (N α) current :=
  rfl

/-- Flux functional generated by velocity and localization of a one-form-like test:
`α ↦ 1/2 {N α, v}`. -/
noncomputable def velocityLocalizationFlux
    (velocity : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (N : OneForm →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁)) :
    OneForm →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁) :=
  (symmetrizedProductRightLinear 𝓗₁ velocity).comp N

@[simp]
theorem velocityLocalizationFlux_apply
    (velocity : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (N : OneForm →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁)) (α : OneForm) :
    velocityLocalizationFlux 𝓗₁ velocity N α =
      symmetrizedProduct (N α) velocity :=
  rfl

/-- Conventional current supplies a local current-density representation whenever the Heisenberg
localization transport is first-order in `d` and the localized one-form operators commute with the
transported quantity.

The assumptions are deliberately explicit. In particular, differential or nonlocal orbital
quantities need not satisfy `hcomm`, so this theorem does not identify their transport with the
conventional current automatically. -/
noncomputable def conventionalCurrentRepresentation
    (ℏ : ℝ) (h : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁))
    (m velocity : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (d : Test →ₗ[ℂ] OneForm)
    (N : OneForm →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁))
    (hvelocity : ConservationLaw.FactorsThroughDifferential d
      (heisenbergLocalizationFunctional 𝓗₁ ℏ h M)
      (velocityLocalizationFlux 𝓗₁ velocity N))
    (hcomm : ∀ α, AlgebraicFock.linearCommutator (N α) m = 0) :
    ConservationLaw.LocalCurrentDensityRepresentation
      d
      (heisenbergTransportFunctional 𝓗₁ ℏ h M m)
      (operatorLocalCurrentPairing 𝓗₁ N) where
  currentDensity := conventionalCurrent 𝓗₁ velocity m
  represents := by
    intro f
    rw [heisenbergTransportFunctional_eq_symmetrizedProductRight_comp]
    simp only [LinearMap.comp_apply]
    rw [hvelocity f]
    simpa [velocityLocalizationFlux, operatorLocalCurrentPairing, conventionalCurrent] using
      symmetrizedProduct_nested_eq_of_commutes 𝓗₁ (N (d f)) velocity m (hcomm (d f))

@[simp]
theorem conventionalCurrentRepresentation_currentDensity
    (ℏ : ℝ) (h : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (M : Test →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁))
    (m velocity : 𝓗₁ →ₗ[ℂ] 𝓗₁)
    (d : Test →ₗ[ℂ] OneForm)
    (N : OneForm →ₗ[ℂ] (𝓗₁ →ₗ[ℂ] 𝓗₁))
    (hvelocity : ConservationLaw.FactorsThroughDifferential d
      (heisenbergLocalizationFunctional 𝓗₁ ℏ h M)
      (velocityLocalizationFlux 𝓗₁ velocity N))
    (hcomm : ∀ α, AlgebraicFock.linearCommutator (N α) m = 0) :
    (conventionalCurrentRepresentation 𝓗₁ ℏ h M m velocity d N hvelocity hcomm).currentDensity =
      conventionalCurrent 𝓗₁ velocity m :=
  rfl

end Field
end Fermionic
end SecondQuantization
