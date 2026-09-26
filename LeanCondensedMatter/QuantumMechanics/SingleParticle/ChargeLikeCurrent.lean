import LeanCondensedMatter.QuantumMechanics.SingleParticle.CorrectedCurrent

set_option linter.style.header false

/-!
# Charge-like specialization of the corrected current

For a transported scalar quantity `q I`, every localization operator commutes with the quantity.
Consequently the generic localization correction vanishes and the symmetrized current density
reduces to `q v`.

This is a theorem about the canonical corrected representative. It does not remove arbitrary full
current-extension data away from exact differentials.
-/

namespace QuantumMechanics
namespace SingleParticle

variable {Test OneForm : Type*}
variable [AddCommGroup Test] [Module ℂ Test]
variable [AddCommGroup OneForm] [Module ℂ OneForm]
variable (V : Type*) [AddCommGroup V] [Module ℂ V]

/-- For a scalar transported quantity, the generic symmetrized flux is the local pairing with
`q • velocity`. -/
theorem symmetrizedCurrentFlux_smul_id_eq_localPairing
    (velocity : V →ₗ[ℂ] V)
    (N : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V))
    (q : ℂ) :
    _root_.ConservationLaw.symmetrizedCurrentFlux
        V velocity (q • LinearMap.id) N =
      operatorLocalCurrentPairing V N (q • velocity) := by
  change operatorLocalCurrentPairing V N
      (_root_.ConservationLaw.symmetrizedProduct velocity (q • LinearMap.id)) =
    operatorLocalCurrentPairing V N (q • velocity)
  rw [_root_.ConservationLaw.symmetrizedProduct_smul_id]

/-- The canonical corrected current functional for a charge-like quantity is exactly the local
pairing with the charge current density `q v`. -/
theorem correctedChargeCurrentFlux_eq
    (velocity : V →ₗ[ℂ] V)
    (N : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V))
    (q : ℂ) :
    _root_.ConservationLaw.nestedSymmetrizedCurrentFlux
        V velocity (q • LinearMap.id) N =
      operatorLocalCurrentPairing V N (q • velocity) := by
  rw [_root_.ConservationLaw.nestedSymmetrizedCurrentFlux_eq_symmetrized_add_correction,
    _root_.ConservationLaw.localizationCorrectionCurrentFlux_smul_id, add_zero]
  exact symmetrizedCurrentFlux_smul_id_eq_localPairing V velocity N q

/-- The chosen corrected differential-current representation reduces to the charge-current pairing
`q v` when the transported quantity is `q I`. -/
theorem correctedSymmetrizedVelocityCurrentRepresentation_smul_id_current
    (ℏ : ℝ) (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (velocity : V →ₗ[ℂ] V)
    (d : Test →ₗ[ℂ] OneForm)
    (N : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V))
    (q : ℂ)
    (hvelocity : _root_.ConservationLaw.FactorsThroughDifferential d
      (heisenbergLocalizationFunctional V ℏ h M)
      (velocityLocalizationFlux V velocity N)) :
    (correctedSymmetrizedVelocityCurrentRepresentation
      V ℏ h M (q • LinearMap.id) velocity d N hvelocity).current =
      operatorLocalCurrentPairing V N (q • velocity) := by
  change
    _root_.ConservationLaw.nestedSymmetrizedCurrentFlux
        V velocity (q • LinearMap.id) N =
      operatorLocalCurrentPairing V N (q • velocity)
  exact correctedChargeCurrentFlux_eq V velocity N q

end SingleParticle
end QuantumMechanics
