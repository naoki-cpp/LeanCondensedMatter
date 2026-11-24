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

/-- The canonical corrected current functional for a charge-like quantity is exactly the local
pairing with the charge current density `q v`. -/
theorem correctedChargeCurrentFlux_eq
    (velocity : V →ₗ[ℂ] V)
    (N : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V))
    (q : ℂ) :
    _root_.ConservationLaw.nestedSymmetrizedCurrentFlux velocity (q • LinearMap.id) N =
      operatorLocalCurrentPairing V N (q • velocity) := by
  have hcorr : _root_.ConservationLaw.localizationCorrectionCurrentFlux
      velocity (q • LinearMap.id) N = 0 := by
    simpa only [Module.End.one_eq_id] using
      (_root_.ConservationLaw.localizationCorrectionCurrentFlux_smul_one velocity N q)
  rw [_root_.ConservationLaw.nestedSymmetrizedCurrentFlux_eq_symmetrized_add_correction,
    hcorr, add_zero]
  apply LinearMap.ext
  intro α
  rw [_root_.ConservationLaw.symmetrizedCurrentFlux_apply,
    operatorLocalCurrentPairing_apply,
    _root_.LinearMap.symmetrizedProduct_smul_id]

/-- The chosen corrected differential-current representation reduces to the charge-current pairing
`q v` when the transported quantity is `q I`. -/
theorem correctedSymmetrizedVelocityCurrentRepresentation_smul_id_current
    (ℏ : ℝ) (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (velocity : V →ₗ[ℂ] V)
    (d : Test →ₗ[ℂ] OneForm)
    (N : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V))
    (q : ℂ)
    (hvelocity : heisenbergLocalizationFunctional V ℏ h M =
      (_root_.ConservationLaw.localizedQuantityFunctional N velocity).comp d) :
    (correctedSymmetrizedVelocityCurrentRepresentation
      V ℏ h M (q • LinearMap.id) velocity d N hvelocity).val =
      operatorLocalCurrentPairing V N (q • velocity) := by
  change
    _root_.ConservationLaw.nestedSymmetrizedCurrentFlux velocity (q • LinearMap.id) N =
      operatorLocalCurrentPairing V N (q • velocity)
  exact correctedChargeCurrentFlux_eq V velocity N q

end SingleParticle
end QuantumMechanics
