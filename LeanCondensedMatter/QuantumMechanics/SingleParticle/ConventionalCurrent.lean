import LeanCondensedMatter.Analysis.Calculus.SymmetricLocalization
import LeanCondensedMatter.QuantumTheory.ConservationLaw.HeisenbergEvolution
import Mathlib.Tactic.Module

set_option linter.style.header false

/-!
# Conventional one-particle current

This module owns the first-quantized specialization of the abstract balance/current machinery.
`Analysis` supplies symmetric localization and differential current factorization, while
`QuantumTheory` supplies only Heisenberg evolution. Here those ingredients are combined with a
model-supplied localization map and, when available, a distinguished velocity `v`.

If

```text
δₕ(M f) = 1/2 {N (d f), v},
```

and the localized one-form operators commute with a one-body quantity `m`, the transport current is

```text
jᵐ = 1/2 {v,m}.
```
-/

namespace QuantumMechanics
namespace SingleParticle

open QuantumTheory.ConservationLaw

variable {Test OneForm : Type*}
variable [AddCommGroup Test] [Module ℂ Test]
variable [AddCommGroup OneForm] [Module ℂ OneForm]
variable (V : Type*) [AddCommGroup V] [Module ℂ V]

/-- The localization commutator scaled to the physical Heisenberg derivative. -/
noncomputable def heisenbergLocalizationFunctional
    (ℏ : ℝ) (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V)) :
    Test →ₗ[ℂ] (V →ₗ[ℂ] V) :=
  heisenbergScale ℏ • _root_.ConservationLaw.localizationCommutatorFunctional V h M

/-- The symmetrically localized transport functional in Heisenberg normalization. -/
noncomputable def heisenbergTransportFunctional
    (ℏ : ℝ) (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m : V →ₗ[ℂ] V) :
    Test →ₗ[ℂ] (V →ₗ[ℂ] V) :=
  heisenbergScale ℏ • _root_.ConservationLaw.transportFunctional V h M m

/-- The symmetrically localized source/torque functional in Heisenberg normalization. -/
noncomputable def heisenbergSourceFunctional
    (ℏ : ℝ) (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m : V →ₗ[ℂ] V) :
    Test →ₗ[ℂ] (V →ₗ[ℂ] V) :=
  heisenbergScale ℏ • _root_.ConservationLaw.sourceFunctional V h M m

@[simp]
theorem heisenbergLocalizationFunctional_apply
    (ℏ : ℝ) (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V)) (f : Test) :
    heisenbergLocalizationFunctional V ℏ h M f =
      heisenbergScale ℏ • _root_.ConservationLaw.linearCommutator h (M f) :=
  rfl

@[simp]
theorem heisenbergTransportFunctional_apply
    (ℏ : ℝ) (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m : V →ₗ[ℂ] V) (f : Test) :
    heisenbergTransportFunctional V ℏ h M m f =
      heisenbergScale ℏ • _root_.ConservationLaw.transportCommutator V h M m f :=
  rfl

@[simp]
theorem heisenbergSourceFunctional_apply
    (ℏ : ℝ) (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m : V →ₗ[ℂ] V) (f : Test) :
    heisenbergSourceFunctional V ℏ h M m f =
      heisenbergScale ℏ • _root_.ConservationLaw.sourceCommutator V h M m f :=
  rfl

/-- Heisenberg scaling commutes with fixed-`m` symmetrization. -/
theorem heisenbergTransportFunctional_eq_symmetrizedProductRight_comp
    (ℏ : ℝ) (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m : V →ₗ[ℂ] V) :
    heisenbergTransportFunctional V ℏ h M m =
      (_root_.ConservationLaw.symmetrizedProductRightLinear V m).comp
        (heisenbergLocalizationFunctional V ℏ h M) := by
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro x
  simp [heisenbergTransportFunctional, heisenbergLocalizationFunctional,
    heisenbergScale, _root_.ConservationLaw.transportFunctional,
    _root_.ConservationLaw.localizationCommutatorFunctional,
    _root_.ConservationLaw.symmetrizedProductRightLinear,
    _root_.ConservationLaw.symmetrizedProduct,
    _root_.ConservationLaw.linearCommutator]
  module

/-- A differential representation of Heisenberg transport together with the canonical source gives
an abstract balance law for the symmetrically localized quantity. -/
noncomputable def heisenbergSymmetricLocalizationBalanceLaw
    (ℏ : ℝ) (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m : V →ₗ[ℂ] V)
    (d : Test →ₗ[ℂ] OneForm)
    (J : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V))
    (hJ : _root_.ConservationLaw.FactorsThroughDifferential d
      (heisenbergTransportFunctional V ℏ h M m) J) :
    _root_.ConservationLaw.BalanceLaw
      (heisenbergEvolution V ℏ h)
      (_root_.ConservationLaw.localizedQuantityFunctional V M m)
      d where
  current := J
  source := heisenbergSourceFunctional V ℏ h M m
  balance := by
    intro f
    rw [hJ f]
    change heisenbergScale ℏ •
        _root_.ConservationLaw.linearCommutator h
          (_root_.ConservationLaw.localizedQuantity V M m f) = _
    rw [_root_.ConservationLaw.linearCommutator_localizedQuantity]
    simp [heisenbergSourceFunctional, heisenbergTransportFunctional, smul_add]

/-- The conventional one-body current operator `jᵐ = 1/2 {v,m}`. -/
noncomputable def conventionalCurrent
    (velocity m : V →ₗ[ℂ] V) : V →ₗ[ℂ] V :=
  _root_.ConservationLaw.symmetrizedProduct velocity m

@[simp]
theorem conventionalCurrent_smul_id
    (velocity : V →ₗ[ℂ] V) (q : ℂ) :
    conventionalCurrent V velocity (q • LinearMap.id) = q • velocity := by
  exact _root_.ConservationLaw.symmetrizedProduct_smul_id velocity q

@[simp]
theorem conventionalCurrent_id
    (velocity : V →ₗ[ℂ] V) :
    conventionalCurrent V velocity LinearMap.id = velocity := by
  simpa using conventionalCurrent_smul_id V velocity (1 : ℂ)

/-- Reassociation identity behind the conventional-current formula. -/
theorem symmetrizedProduct_nested_eq_of_commutes
    (localizer velocity m : V →ₗ[ℂ] V)
    (hcomm : _root_.ConservationLaw.linearCommutator localizer m = 0) :
    _root_.ConservationLaw.symmetrizedProduct
        (_root_.ConservationLaw.symmetrizedProduct localizer velocity) m =
      _root_.ConservationLaw.symmetrizedProduct localizer
        (_root_.ConservationLaw.symmetrizedProduct velocity m) := by
  apply LinearMap.ext
  intro x
  have hlocalizer (y : V) : localizer (m y) = m (localizer y) := by
    have h := congrArg (fun T : V →ₗ[ℂ] V => T y) hcomm
    have hzero : localizer (m y) - m (localizer y) = 0 := by
      simpa [_root_.ConservationLaw.linearCommutator] using h
    exact sub_eq_zero.mp hzero
  simp [_root_.ConservationLaw.symmetrizedProduct, hlocalizer]
  module

/-- A one-form-like test is paired with a one-body current operator by symmetric localization. -/
noncomputable def operatorLocalCurrentPairing
    (N : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V)) :
    _root_.ConservationLaw.LocalCurrentPairing
      (𝕜 := ℂ)
      (OneForm := OneForm)
      (Obs := V →ₗ[ℂ] V)
      (CurrentDensity := V →ₗ[ℂ] V) where
  toFun := fun current =>
    (_root_.ConservationLaw.symmetrizedProductRightLinear V current).comp N
  map_add' := by
    intro j₁ j₂
    apply LinearMap.ext
    intro α
    apply LinearMap.ext
    intro x
    simp [_root_.ConservationLaw.symmetrizedProductRightLinear,
      _root_.ConservationLaw.symmetrizedProduct]
    module
  map_smul' := by
    intro c j
    apply LinearMap.ext
    intro α
    apply LinearMap.ext
    intro x
    simp [_root_.ConservationLaw.symmetrizedProductRightLinear,
      _root_.ConservationLaw.symmetrizedProduct]
    module

@[simp]
theorem operatorLocalCurrentPairing_apply
    (N : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V))
    (current : V →ₗ[ℂ] V) (α : OneForm) :
    operatorLocalCurrentPairing V N current α =
      _root_.ConservationLaw.symmetrizedProduct (N α) current :=
  rfl

/-- Flux functional generated by a concrete one-particle velocity and localized one-form test. -/
noncomputable def velocityLocalizationFlux
    (velocity : V →ₗ[ℂ] V)
    (N : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V)) :
    OneForm →ₗ[ℂ] (V →ₗ[ℂ] V) :=
  (_root_.ConservationLaw.symmetrizedProductRightLinear V velocity).comp N

@[simp]
theorem velocityLocalizationFlux_apply
    (velocity : V →ₗ[ℂ] V)
    (N : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V)) (α : OneForm) :
    velocityLocalizationFlux V velocity N α =
      _root_.ConservationLaw.symmetrizedProduct (N α) velocity :=
  rfl

/-- Conventional current supplies a local current-density representation whenever the Heisenberg
localization transport is first-order in `d` and the localized one-form operators commute with the
transported quantity. -/
noncomputable def conventionalCurrentRepresentation
    (ℏ : ℝ) (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m velocity : V →ₗ[ℂ] V)
    (d : Test →ₗ[ℂ] OneForm)
    (N : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V))
    (hvelocity : _root_.ConservationLaw.FactorsThroughDifferential d
      (heisenbergLocalizationFunctional V ℏ h M)
      (velocityLocalizationFlux V velocity N))
    (hcomm : ∀ α, _root_.ConservationLaw.linearCommutator (N α) m = 0) :
    _root_.ConservationLaw.LocalCurrentDensityRepresentation
      d
      (heisenbergTransportFunctional V ℏ h M m)
      (operatorLocalCurrentPairing V N) where
  currentDensity := conventionalCurrent V velocity m
  represents := by
    intro f
    rw [heisenbergTransportFunctional_eq_symmetrizedProductRight_comp]
    simp only [LinearMap.comp_apply]
    rw [hvelocity f]
    simpa [velocityLocalizationFlux, operatorLocalCurrentPairing, conventionalCurrent] using
      symmetrizedProduct_nested_eq_of_commutes V (N (d f)) velocity m (hcomm (d f))

@[simp]
theorem conventionalCurrentRepresentation_currentDensity
    (ℏ : ℝ) (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m velocity : V →ₗ[ℂ] V)
    (d : Test →ₗ[ℂ] OneForm)
    (N : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V))
    (hvelocity : _root_.ConservationLaw.FactorsThroughDifferential d
      (heisenbergLocalizationFunctional V ℏ h M)
      (velocityLocalizationFlux V velocity N))
    (hcomm : ∀ α, _root_.ConservationLaw.linearCommutator (N α) m = 0) :
    (conventionalCurrentRepresentation V ℏ h M m velocity d N hvelocity hcomm).currentDensity =
      conventionalCurrent V velocity m :=
  rfl

end SingleParticle
end QuantumMechanics
