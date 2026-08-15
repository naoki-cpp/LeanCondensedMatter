import LeanCondensedMatter.QuantumTheory.ConservationLaw.CurrentRepresentation
import Mathlib.Tactic.Module

set_option linter.style.header false

/-!
# Heisenberg-scaled one-body transport

This module converts the algebraic commutator transport functional into the physical Heisenberg
normalization

```text
δₕ(A) = (i / ℏ) [h,A].
```

It remains independent of any particular current-density representation and of second quantization.
-/

namespace QuantumTheory
namespace ConservationLaw

variable {Test : Type*} [AddCommGroup Test] [Module ℂ Test]
variable (V : Type*) [AddCommGroup V] [Module ℂ V]

/-- Scalar converting a commutator with the Hamiltonian into the Heisenberg derivative. -/
noncomputable def heisenbergScale (ℏ : ℝ) : ℂ :=
  Complex.I / (ℏ : ℂ)

/-- The localization commutator functional scaled to the physical Heisenberg derivative. -/
noncomputable def heisenbergLocalizationFunctional
    (ℏ : ℝ) (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V)) :
    Test →ₗ[ℂ] (V →ₗ[ℂ] V) :=
  heisenbergScale ℏ • localizationCommutatorFunctional V h M

/-- The generalized transport functional scaled to the physical Heisenberg derivative. -/
noncomputable def heisenbergTransportFunctional
    (ℏ : ℝ) (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m : V →ₗ[ℂ] V) :
    Test →ₗ[ℂ] (V →ₗ[ℂ] V) :=
  heisenbergScale ℏ • transportFunctional V h M m

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

/-- Heisenberg scaling commutes with the fixed-`m` symmetrization that builds generalized transport
from bare localization transport. -/
theorem heisenbergTransportFunctional_eq_symmetrizedProductRight_comp
    (ℏ : ℝ) (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m : V →ₗ[ℂ] V) :
    heisenbergTransportFunctional V ℏ h M m =
      (symmetrizedProductRightLinear V m).comp
        (heisenbergLocalizationFunctional V ℏ h M) := by
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro x
  simp [heisenbergTransportFunctional, heisenbergLocalizationFunctional,
    heisenbergScale, transportFunctional, _root_.ConservationLaw.transportCommutator,
    localizationCommutatorFunctional, symmetrizedProductRightLinear,
    _root_.ConservationLaw.symmetrizedProduct, _root_.ConservationLaw.linearCommutator]
  module

end ConservationLaw
end QuantumTheory
