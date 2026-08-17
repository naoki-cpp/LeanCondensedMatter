import LeanCondensedMatter.QuantumMechanics.SingleParticle.SymmetrizedVelocityCurrent

set_option linter.style.header false

/-!
# Conventional-current terminology

This module retains the historical condensed-matter name "conventional current" for the
symmetrized velocity current

```text
jᵐ = 1/2 {v,m}.
```

The name is intentionally a compatibility/interpretation layer. The transport functional and its
local pairing live in `LocalizedTransport`, while the neutral current-density construction and the
conditions under which it represents transport live in `SymmetrizedVelocityCurrent`.

In particular, importing this module must not be necessary to formulate one-particle transport.
-/

namespace QuantumMechanics
namespace SingleParticle

variable {Test OneForm : Type*}
variable [AddCommGroup Test] [Module ℂ Test]
variable [AddCommGroup OneForm] [Module ℂ OneForm]
variable (V : Type*) [AddCommGroup V] [Module ℂ V]

/-- Historical name for the symmetrized velocity current `1/2 {v,m}`. -/
noncomputable def conventionalCurrent
    (velocity m : V →ₗ[ℂ] V) : V →ₗ[ℂ] V :=
  symmetrizedVelocityCurrent V velocity m

@[simp]
theorem conventionalCurrent_smul_id
    (velocity : V →ₗ[ℂ] V) (q : ℂ) :
    conventionalCurrent V velocity (q • LinearMap.id) = q • velocity := by
  exact symmetrizedVelocityCurrent_smul_id V velocity q

@[simp]
theorem conventionalCurrent_id
    (velocity : V →ₗ[ℂ] V) :
    conventionalCurrent V velocity LinearMap.id = velocity := by
  exact symmetrizedVelocityCurrent_id V velocity

/-- Compatibility spelling of the commutative nested-symmetrization identity. -/
theorem symmetrizedProduct_nested_eq_of_commutes
    (localizer velocity m : V →ₗ[ℂ] V)
    (hcomm : _root_.ConservationLaw.linearCommutator localizer m = 0) :
    _root_.ConservationLaw.symmetrizedProduct
        (_root_.ConservationLaw.symmetrizedProduct localizer velocity) m =
      _root_.ConservationLaw.symmetrizedProduct localizer
        (_root_.ConservationLaw.symmetrizedProduct velocity m) := by
  exact _root_.ConservationLaw.symmetrizedProduct_nested_eq_of_commutes
    localizer velocity m hcomm

/-- Historical-name wrapper for `symmetrizedVelocityCurrentRepresentation`. -/
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
      (operatorLocalCurrentPairing V N) :=
  symmetrizedVelocityCurrentRepresentation V ℏ h M m velocity d N hvelocity hcomm

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
      conventionalCurrent V velocity m := by
  rfl

end SingleParticle
end QuantumMechanics
