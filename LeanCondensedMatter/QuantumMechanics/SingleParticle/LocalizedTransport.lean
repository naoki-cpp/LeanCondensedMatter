import LeanCondensedMatter.Analysis.ConservationLaw.CurrentRepresentation
import LeanCondensedMatter.Analysis.ConservationLaw.FluxBalanceLaw
import LeanCondensedMatter.Analysis.ConservationLaw.SymmetricLocalizationAlgebra
import LeanCondensedMatter.QuantumTheory.ConservationLaw.HeisenbergEvolution

set_option linter.style.header false

/-!
# Localized one-particle transport

This module owns the first-quantized specialization of the abstract balance/current machinery.
`Analysis` supplies symmetric localization and differential current factorization, while
`QuantumTheory` supplies only Heisenberg evolution. Here those ingredients are combined with a
model-supplied localization map and, when available, a distinguished velocity.

No particular current-density formula is selected here. The fundamental transport object is the
functional on differential test data. A formula such as `1/2 {v,m}` is a downstream representation
of that functional under additional assumptions.
-/

namespace QuantumMechanics
namespace SingleParticle

attribute [local instance 100] LieRing.ofAssociativeRing

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
  (heisenbergEvolution ℏ h).comp M

/-- The symmetrically localized transport functional in Heisenberg normalization. -/
noncomputable def heisenbergTransportFunctional
    (ℏ : ℝ) (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m : V →ₗ[ℂ] V) :
    Test →ₗ[ℂ] (V →ₗ[ℂ] V) :=
  _root_.ConservationLaw.localizedQuantityFunctional (heisenbergLocalizationFunctional V ℏ h M) m

/-- The symmetrically localized source/torque functional in Heisenberg normalization. -/
noncomputable def heisenbergSourceFunctional
    (ℏ : ℝ) (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m : V →ₗ[ℂ] V) :
    Test →ₗ[ℂ] (V →ₗ[ℂ] V) :=
  _root_.ConservationLaw.localizedQuantityFunctional M (heisenbergEvolution ℏ h m)

@[simp]
theorem heisenbergLocalizationFunctional_apply
    (ℏ : ℝ) (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V)) (f : Test) :
    heisenbergLocalizationFunctional V ℏ h M f =
      heisenbergScale ℏ • ⁅h, M f⁆ :=
  rfl

@[simp]
theorem heisenbergTransportFunctional_apply
    (ℏ : ℝ) (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m : V →ₗ[ℂ] V) (f : Test) :
    heisenbergTransportFunctional V ℏ h M m f =
      _root_.LinearMap.symmetrizedProduct (K := ℂ) (heisenbergEvolution ℏ h (M f)) m :=
  rfl

@[simp]
theorem heisenbergSourceFunctional_apply
    (ℏ : ℝ) (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m : V →ₗ[ℂ] V) (f : Test) :
    heisenbergSourceFunctional V ℏ h M m f =
      _root_.LinearMap.symmetrizedProduct (K := ℂ) (M f) (heisenbergEvolution ℏ h m) :=
  rfl

/-- Heisenberg evolution of a symmetrically localized one-body quantity gives the intrinsic balance
law as soon as its transport functional depends only on differential test data.  No extension of
that transport to arbitrary one-form-like data is chosen here. -/
noncomputable def heisenbergIntrinsicSymmetricLocalizationBalanceLaw
    (ℏ : ℝ) (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m : V →ₗ[ℂ] V)
    (d : Test →ₗ[ℂ] OneForm)
    (htransport : Function.FactorsThrough
      (heisenbergTransportFunctional V ℏ h M m) d) :
    _root_.ConservationLaw.FluxBalanceLaw
      (heisenbergEvolution ℏ h)
      (_root_.ConservationLaw.localizedQuantityFunctional M m)
      d where
  transport := heisenbergTransportFunctional V ℏ h M m
  transport_depends := htransport
  source := heisenbergSourceFunctional V ℏ h M m
  balance := by
    apply LinearMap.ext
    intro f
    exact heisenbergEvolution_symmetrizedProduct ℏ h (M f) m

/-- A one-form-like test is paired with a one-body current-density operator by symmetric
localization. This pairing does not choose which current density represents a given transport
functional. -/
noncomputable def operatorLocalCurrentPairing
    (N : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V)) :
    _root_.ConservationLaw.LocalCurrentPairing
      (𝕜 := ℂ)
      (OneForm := OneForm)
      (Obs := V →ₗ[ℂ] V)
      (CurrentDensity := V →ₗ[ℂ] V) :=
  ((LinearMap.llcomp ℂ OneForm (V →ₗ[ℂ] V) (V →ₗ[ℂ] V)).flip N).comp
    (LinearMap.flip (_root_.LinearMap.symmetrizedProductBilinear (K := ℂ) (V →ₗ[ℂ] V)))

@[simp]
theorem operatorLocalCurrentPairing_apply
    (N : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V))
    (current : V →ₗ[ℂ] V) (α : OneForm) :
    operatorLocalCurrentPairing V N current α =
      _root_.LinearMap.symmetrizedProduct (K := ℂ) (N α) current :=
  rfl

end SingleParticle
end QuantumMechanics
