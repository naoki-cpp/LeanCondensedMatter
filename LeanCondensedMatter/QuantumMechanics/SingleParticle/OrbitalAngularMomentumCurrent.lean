import LeanCondensedMatter.QuantumMechanics.SingleParticle.OrbitalAngularMomentum
import LeanCondensedMatter.QuantumMechanics.SingleParticle.CorrectedCurrent

set_option linter.style.header false

/-!
# Orbital angular momentum in the weak-current representation

Connect the existing continuum-like orbital-localizer commutator to the canonical
symmetrized-current correction and its Heisenberg transport functional.

The correction need not vanish when a localizer fails to commute with orbital angular momentum:
it vanishes precisely when the *velocity* commutes with that orbital-localization obstruction.
These are algebraic statements on a shared operator domain, not a unique local current-density
formula, an unbounded continuum realization, or a torque-dipole (proper-current) identity.
-/

namespace QuantumMechanics
namespace SingleParticle

attribute [local instance 100] LieRing.ofAssociativeRing

variable {V OneForm : Type*}
variable [AddCommGroup V] [Module ℂ V]
variable [AddCommGroup OneForm] [Module ℂ OneForm]

/-- For `L_z = X P_y - Y P_x`, identify the *existing* localization-current correction
with the commutator of the velocity and the derivative-localizer obstruction.
The coefficient `c` can be instantiated with `iℏ` in the continuum-sign convention. -/
theorem orbitalAngularMomentumZ_localizationCorrectionCurrentFlux_apply
    (velocity X Y Px Py : V →ₗ[ℂ] V)
    (N : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V))
    (α : OneForm) (Dx Dy : V →ₗ[ℂ] V) (c : ℂ)
    (hX : ⁅N α, X⁆ = 0) (hY : ⁅N α, Y⁆ = 0)
    (hPx : ⁅N α, Px⁆ = c • Dx)
    (hPy : ⁅N α, Py⁆ = c • Dy) :
    _root_.ConservationLaw.localizationCorrectionCurrentFlux V velocity
        (orbitalAngularMomentumZ X Y Px Py) N α =
      (1 / 4 : ℂ) • ⁅velocity, X.comp (c • Dy) - Y.comp (c • Dx)⁆ := by
  rw [_root_.ConservationLaw.localizationCorrectionCurrentFlux_apply]
  rw [lie_orbitalAngularMomentumZ_of_derivative_localizers
    (N α) X Y Px Py Dx Dy c hX hY hPx hPy]

/-- Noncommutation of a localizer with `L_z` alone does *not* imply a nonzero
current correction. The exact criterion is the *double* commutator with velocity. -/
theorem orbitalAngularMomentumZ_localizationCorrectionCurrentFlux_ne_zero_iff
    (velocity X Y Px Py : V →ₗ[ℂ] V)
    (N : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V))
    (α : OneForm) (Dx Dy : V →ₗ[ℂ] V) (c : ℂ)
    (hX : ⁅N α, X⁆ = 0) (hY : ⁅N α, Y⁆ = 0)
    (hPx : ⁅N α, Px⁆ = c • Dx)
    (hPy : ⁅N α, Py⁆ = c • Dy) :
    _root_.ConservationLaw.localizationCorrectionCurrentFlux V velocity
        (orbitalAngularMomentumZ X Y Px Py) N α ≠ 0 ↔
      ⁅velocity, X.comp (c • Dy) - Y.comp (c • Dx)⁆ ≠ 0 := by
  rw [orbitalAngularMomentumZ_localizationCorrectionCurrentFlux_apply
    velocity X Y Px Py N α Dx Dy c hX hY hPx hPy]
  simp

variable {Test : Type*} [AddCommGroup Test] [Module ℂ Test]

/-- At an exact differential `d f`, the canonical one-body Heisenberg transport equals
the conventional symmetrized flux plus the explicit orbital-localization correction.
The velocity representation is an explicit physical hypothesis; no local density is chosen. -/
theorem heisenbergTransportOrbitalAngularMomentumZ_apply
    (ℏ : ℝ) (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (X Y Px Py velocity : V →ₗ[ℂ] V)
    (d : Test →ₗ[ℂ] OneForm)
    (N : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V))
    (f : Test) (Dx Dy : V →ₗ[ℂ] V) (c : ℂ)
    (hvelocity : heisenbergLocalizationFunctional V ℏ h M =
      (velocityLocalizationFlux V velocity N).comp d)
    (hX : ⁅N (d f), X⁆ = 0) (hY : ⁅N (d f), Y⁆ = 0)
    (hPx : ⁅N (d f), Px⁆ = c • Dx)
    (hPy : ⁅N (d f), Py⁆ = c • Dy) :
    heisenbergTransportFunctional V ℏ h M (orbitalAngularMomentumZ X Y Px Py) f =
      _root_.ConservationLaw.symmetrizedCurrentFlux V velocity
          (orbitalAngularMomentumZ X Y Px Py) N (d f) +
        (1 / 4 : ℂ) • ⁅velocity, X.comp (c • Dy) - Y.comp (c • Dx)⁆ := by
  calc
    _ = _root_.ConservationLaw.nestedSymmetrizedCurrentFlux V velocity
        (orbitalAngularMomentumZ X Y Px Py) N (d f) := by
          simpa only [LinearMap.comp_apply] using congrArg
            (fun Φ : Test →ₗ[ℂ] (V →ₗ[ℂ] V) => Φ f)
            (nestedSymmetrizedCurrentFlux_eq_comp V ℏ h M
              (orbitalAngularMomentumZ X Y Px Py) velocity d N hvelocity)
    _ = _ := by
      rw [_root_.ConservationLaw.nestedSymmetrizedCurrentFlux_eq_symmetrized_add_correction]
      simp only [LinearMap.add_apply]
      rw [orbitalAngularMomentumZ_localizationCorrectionCurrentFlux_apply
        velocity X Y Px Py N (d f) Dx Dy c hX hY hPx hPy]

end SingleParticle
end QuantumMechanics
