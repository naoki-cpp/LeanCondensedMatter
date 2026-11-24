import LeanCondensedMatter.QuantumMechanics.SingleParticle.GeneralizedCurrent
import LeanCondensedMatter.QuantumMechanics.SingleParticle.CorrectedCurrent

set_option linter.style.header false

/-!
# Localized representation of the symmetrized velocity current

The operator-level generalized current `jᵐ = 1/2 {v,m}` is owned independently by
`SingleParticle.GeneralizedCurrent`. This module adds localization semantics: it proves when that
operator represents the exact-differential transport supplied by a Heisenberg balance law.

Without commutation between the localized one-form operator and `m`, nested symmetrization carries
a double-commutator correction (`LinearMap.symmetrizedProduct_nested`). The general
representation is supplied by `nestedSymmetrizedCurrentFlux_eq_comp`; here the vanishing
correction gives a special current-density
representation, not a universal transport law.
-/

namespace QuantumMechanics
namespace SingleParticle

attribute [local instance 100] LieRing.ofAssociativeRing

variable {Test OneForm : Type*}
variable [AddCommGroup Test] [Module ℂ Test]
variable [AddCommGroup OneForm] [Module ℂ OneForm]
variable (V : Type*) [AddCommGroup V] [Module ℂ V]

/-- The symmetrized velocity current supplies a local current-density representation whenever the
Heisenberg localization transport is first-order in `d` and the localized one-form operators
commute with the transported quantity. -/
noncomputable def symmetrizedVelocityCurrentRepresentation
    (ℏ : ℝ) (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m velocity : V →ₗ[ℂ] V)
    (d : Test →ₗ[ℂ] OneForm)
    (N : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V))
    (hvelocity : heisenbergLocalizationFunctional V ℏ h M =
      (_root_.ConservationLaw.localizedQuantityFunctional N velocity).comp d)
    (hcomm : ∀ α, ⁅N α, m⁆ = 0) :
    _root_.ConservationLaw.LocalCurrentDensityRepresentation
      d
      (heisenbergTransportFunctional V ℏ h M m)
      (operatorLocalCurrentPairing V N) where
  val := symmetrizedVelocityCurrent V velocity m
  property := by
    change heisenbergTransportFunctional V ℏ h M m =
      (_root_.ConservationLaw.symmetrizedCurrentFlux velocity m N).comp d
    rw [nestedSymmetrizedCurrentFlux_eq_comp V ℏ h M m velocity d N hvelocity,
      _root_.ConservationLaw.nestedSymmetrizedCurrentFlux_eq_symmetrized_add_correction,
      _root_.ConservationLaw.localizationCorrectionCurrentFlux_eq_zero_of_commutes
        velocity m N hcomm, add_zero]

@[simp]
theorem symmetrizedVelocityCurrentRepresentation_currentDensity
    (ℏ : ℝ) (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m velocity : V →ₗ[ℂ] V)
    (d : Test →ₗ[ℂ] OneForm)
    (N : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V))
    (hvelocity : heisenbergLocalizationFunctional V ℏ h M =
      (_root_.ConservationLaw.localizedQuantityFunctional N velocity).comp d)
    (hcomm : ∀ α, ⁅N α, m⁆ = 0) :
    (symmetrizedVelocityCurrentRepresentation V ℏ h M m velocity d N hvelocity hcomm).val =
      symmetrizedVelocityCurrent V velocity m :=
  rfl

end SingleParticle
end QuantumMechanics
