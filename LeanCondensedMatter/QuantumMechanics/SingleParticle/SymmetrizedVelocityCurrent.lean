import LeanCondensedMatter.QuantumMechanics.SingleParticle.LocalizedTransport

set_option linter.style.header false

/-!
# Symmetrized velocity-current representation

For a distinguished one-particle velocity `v` and quantity `m`, the operator

```text
1/2 {v,m}
```

is a useful Hermitian current-density candidate. It is not taken here as the definition of current:
the fundamental transport object remains the differential current functional supplied by the
balance law. This module only proves when the symmetrized velocity operator represents that
functional relative to the local pairing.

Without commutation between the localized one-form operator and `m`, nested symmetrization carries
a double-commutator correction. Thus the symmetrized velocity current is a special current-density
representation, not a universal transport law.
-/

namespace QuantumMechanics
namespace SingleParticle

variable {Test OneForm : Type*}
variable [AddCommGroup Test] [Module ℂ Test]
variable [AddCommGroup OneForm] [Module ℂ OneForm]
variable (V : Type*) [AddCommGroup V] [Module ℂ V]

/-- The symmetrized velocity current-density candidate `1/2 {v,m}`. -/
noncomputable def symmetrizedVelocityCurrent
    (velocity m : V →ₗ[ℂ] V) : V →ₗ[ℂ] V :=
  _root_.ConservationLaw.symmetrizedProduct velocity m

@[simp]
theorem symmetrizedVelocityCurrent_smul_id
    (velocity : V →ₗ[ℂ] V) (q : ℂ) :
    symmetrizedVelocityCurrent V velocity (q • LinearMap.id) = q • velocity := by
  exact _root_.ConservationLaw.symmetrizedProduct_smul_id velocity q

@[simp]
theorem symmetrizedVelocityCurrent_id
    (velocity : V →ₗ[ℂ] V) :
    symmetrizedVelocityCurrent V velocity LinearMap.id = velocity := by
  simpa using symmetrizedVelocityCurrent_smul_id V velocity (1 : ℂ)

/-- General localized-transport decomposition. The second term measures the failure of the
localized one-form operator to commute with the transported quantity. -/
theorem symmetrizedVelocityTransport_decomposition
    (localizer velocity m : V →ₗ[ℂ] V) :
    _root_.ConservationLaw.symmetrizedProduct
        (_root_.ConservationLaw.symmetrizedProduct localizer velocity) m =
      _root_.ConservationLaw.symmetrizedProduct localizer
        (symmetrizedVelocityCurrent V velocity m) +
      (1 / 4 : ℂ) • _root_.ConservationLaw.linearCommutator velocity
        (_root_.ConservationLaw.linearCommutator localizer m) := by
  simpa [symmetrizedVelocityCurrent] using
    (_root_.ConservationLaw.symmetrizedProduct_nested localizer velocity m)

/-- If localization commutes with the transported quantity, the correction vanishes and the
transport is represented by the symmetrized velocity current density. -/
theorem symmetrizedVelocityTransport_eq_of_localizer_commutes
    (localizer velocity m : V →ₗ[ℂ] V)
    (hcomm : _root_.ConservationLaw.linearCommutator localizer m = 0) :
    _root_.ConservationLaw.symmetrizedProduct
        (_root_.ConservationLaw.symmetrizedProduct localizer velocity) m =
      _root_.ConservationLaw.symmetrizedProduct localizer
        (symmetrizedVelocityCurrent V velocity m) := by
  simpa [symmetrizedVelocityCurrent] using
    (_root_.ConservationLaw.symmetrizedProduct_nested_eq_of_commutes
      localizer velocity m hcomm)

/-- The symmetrized velocity current supplies a local current-density representation whenever the
Heisenberg localization transport is first-order in `d` and the localized one-form operators
commute with the transported quantity. -/
noncomputable def symmetrizedVelocityCurrentRepresentation
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
  currentDensity := symmetrizedVelocityCurrent V velocity m
  represents := by
    intro f
    rw [heisenbergTransportFunctional_eq_symmetrizedProductRight_comp]
    simp only [LinearMap.comp_apply]
    rw [hvelocity f]
    simpa [velocityLocalizationFlux, operatorLocalCurrentPairing] using
      symmetrizedVelocityTransport_eq_of_localizer_commutes
        V (N (d f)) velocity m (hcomm (d f))

@[simp]
theorem symmetrizedVelocityCurrentRepresentation_currentDensity
    (ℏ : ℝ) (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m velocity : V →ₗ[ℂ] V)
    (d : Test →ₗ[ℂ] OneForm)
    (N : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V))
    (hvelocity : _root_.ConservationLaw.FactorsThroughDifferential d
      (heisenbergLocalizationFunctional V ℏ h M)
      (velocityLocalizationFlux V velocity N))
    (hcomm : ∀ α, _root_.ConservationLaw.linearCommutator (N α) m = 0) :
    (symmetrizedVelocityCurrentRepresentation V ℏ h M m velocity d N hvelocity hcomm).currentDensity =
      symmetrizedVelocityCurrent V velocity m :=
  rfl

end SingleParticle
end QuantumMechanics
