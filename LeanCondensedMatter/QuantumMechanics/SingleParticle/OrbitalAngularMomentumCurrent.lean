import LeanCondensedMatter.QuantumMechanics.SingleParticle.OrbitalAngularMomentum
import LeanCondensedMatter.QuantumMechanics.SingleParticle.CorrectedCurrent

set_option linter.style.header false

/-!
# Orbital angular momentum in the weak-current representation

The orbital component is taken in any oriented plane of the complexified
direction space. Its localization commutator feeds the canonical generic
symmetrized-current correction and the Heisenberg transport functional.

A nonzero orbital-localization commutator does not by itself imply a
nonzero current correction: the velocity must fail to commute with the
localization obstruction. These are algebraic operator identities, not
a unique local current density, unbounded continuum realization, or
torque-dipole (proper-current) identity.
-/

namespace QuantumMechanics
namespace SingleParticle

attribute [local instance 100] LieRing.ofAssociativeRing

variable {E V OneForm : Type*}
variable [AddCommGroup E] [Module ℂ E]
variable [AddCommGroup V] [Module ℂ V]
variable [AddCommGroup OneForm] [Module ℂ OneForm]

/-- The orbital localization-current correction for arbitrary directions
`u,v`, expressed by the velocity commutator with the directional
derivative-localizer obstruction. -/
theorem orbitalAngularMomentum_localizationCorrectionCurrentFlux_apply
    (velocity : V →ₗ[ℂ] V) (X P : E →ₗ[ℂ] (V →ₗ[ℂ] V)) (u v : E)
    (N : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V))
    (α : OneForm) (Du Dv : V →ₗ[ℂ] V) (c : ℂ)
    (hXu : ⁅N α, X u⁆ = 0) (hXv : ⁅N α, X v⁆ = 0)
    (hPu : ⁅N α, P u⁆ = c • Du)
    (hPv : ⁅N α, P v⁆ = c • Dv) :
    _root_.ConservationLaw.localizationCorrectionCurrentFlux V velocity
        (orbitalAngularMomentum X P u v) N α =
      (1 / 4 : ℂ) • ⁅velocity, (X u).comp (c • Dv) - (X v).comp (c • Du)⁆ := by
  rw [_root_.ConservationLaw.localizationCorrectionCurrentFlux_apply]
  rw [lie_orbitalAngularMomentum_of_derivative_localizers
    (N α) X P u v Du Dv c hXu hXv hPu hPv]

/-- Exact nonvanishing criterion for the *double* commutator. A
localizer's noncommutation with orbital angular momentum alone is
not sufficient for a nonzero current correction. -/
theorem orbitalAngularMomentum_localizationCorrectionCurrentFlux_ne_zero_iff
    (velocity : V →ₗ[ℂ] V) (X P : E →ₗ[ℂ] (V →ₗ[ℂ] V)) (u v : E)
    (N : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V))
    (α : OneForm) (Du Dv : V →ₗ[ℂ] V) (c : ℂ)
    (hXu : ⁅N α, X u⁆ = 0) (hXv : ⁅N α, X v⁆ = 0)
    (hPu : ⁅N α, P u⁆ = c • Du)
    (hPv : ⁅N α, P v⁆ = c • Dv) :
    _root_.ConservationLaw.localizationCorrectionCurrentFlux V velocity
        (orbitalAngularMomentum X P u v) N α ≠ 0 ↔
      ⁅velocity, (X u).comp (c • Dv) - (X v).comp (c • Du)⁆ ≠ 0 := by
  rw [orbitalAngularMomentum_localizationCorrectionCurrentFlux_apply
    velocity X P u v N α Du Dv c hXu hXv hPu hPv]
  simp

variable {Test : Type*} [AddCommGroup Test] [Module ℂ Test]

/-- At an exact differential `d f`, the one-body Heisenberg transport of an
arbitrary orbital plane component equals its symmetrized flux plus the
explicit orbital-localization correction. The velocity representation
is an explicit physical hypothesis. -/
theorem heisenbergTransportOrbitalAngularMomentum_apply
    (ℏ : ℝ) (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (X P : E →ₗ[ℂ] (V →ₗ[ℂ] V)) (u v : E)
    (velocity : V →ₗ[ℂ] V)
    (d : Test →ₗ[ℂ] OneForm)
    (N : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V))
    (f : Test) (Du Dv : V →ₗ[ℂ] V) (c : ℂ)
    (hvelocity : heisenbergLocalizationFunctional V ℏ h M =
      (velocityLocalizationFlux V velocity N).comp d)
    (hXu : ⁅N (d f), X u⁆ = 0) (hXv : ⁅N (d f), X v⁆ = 0)
    (hPu : ⁅N (d f), P u⁆ = c • Du)
    (hPv : ⁅N (d f), P v⁆ = c • Dv) :
    heisenbergTransportFunctional V ℏ h M (orbitalAngularMomentum X P u v) f =
      _root_.ConservationLaw.symmetrizedCurrentFlux V velocity
          (orbitalAngularMomentum X P u v) N (d f) +
        (1 / 4 : ℂ) • ⁅velocity, (X u).comp (c • Dv) - (X v).comp (c • Du)⁆ := by
  calc
    _ = _root_.ConservationLaw.nestedSymmetrizedCurrentFlux V velocity
        (orbitalAngularMomentum X P u v) N (d f) := by
          simpa only [LinearMap.comp_apply] using congrArg
            (fun Φ : Test →ₗ[ℂ] (V →ₗ[ℂ] V) => Φ f)
            (nestedSymmetrizedCurrentFlux_eq_comp V ℏ h M
              (orbitalAngularMomentum X P u v) velocity d N hvelocity)
    _ = _ := by
      rw [_root_.ConservationLaw.nestedSymmetrizedCurrentFlux_eq_symmetrized_add_correction]
      simp only [LinearMap.add_apply]
      rw [orbitalAngularMomentum_localizationCorrectionCurrentFlux_apply
        velocity X P u v N (d f) Du Dv c hXu hXv hPu hPv]

end SingleParticle
end QuantumMechanics
