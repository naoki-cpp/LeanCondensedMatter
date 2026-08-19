import LeanCondensedMatter.QuantumMechanics.SingleParticle.CorrectedCurrent

set_option linter.style.header false

/-!
# Extension ambiguity of the corrected current

This module states the general current result in the form most directly used in physics: every full
current functional representing the same intrinsic transport is the symmetrized/conventional flux
plus the canonical localization correction, up to a functional that vanishes on exact
differentials.
-/

namespace QuantumMechanics
namespace SingleParticle

variable {Test OneForm : Type*}
variable [AddCommGroup Test] [Module ℂ Test]
variable [AddCommGroup OneForm] [Module ℂ OneForm]
variable (V : Type*) [AddCommGroup V] [Module ℂ V]

/-- Any representative of the same intrinsic transport has the form

`J = J_sym + J_corr + K`

with `K (d f) = 0` for every test object `f`.  Thus `K` is pure extension ambiguity invisible to the
intrinsic flux. -/
theorem exists_current_eq_symmetrized_add_correction_add_invisible
    (ℏ : ℝ) (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m velocity : V →ₗ[ℂ] V)
    (d : Test →ₗ[ℂ] OneForm)
    (N : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V))
    (hvelocity : _root_.ConservationLaw.FactorsThroughDifferential d
      (heisenbergLocalizationFunctional V ℏ h M)
      (velocityLocalizationFlux V velocity N))
    (R : _root_.ConservationLaw.DifferentialCurrentRepresentation d
      (heisenbergTransportFunctional V ℏ h M m)) :
    ∃ K : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V),
      _root_.ConservationLaw.DifferentialCurrentInvisible d K ∧
        R.current =
          (symmetrizedVelocityCurrentFlux V velocity m N +
            localizationCorrectionFlux V velocity m N) + K := by
  exact R.exists_current_eq_add_invisible
    (correctedSymmetrizedVelocityCurrentRepresentation
      V ℏ h M m velocity d N hvelocity)

end SingleParticle
end QuantumMechanics
