import LeanCondensedMatter.QuantumMechanics.SingleParticle.CorrectedCurrent

set_option linter.style.header false

/-!
# Charge-like specialization of the corrected current

For a transported scalar quantity `q I`, every localization operator commutes with the quantity.
Consequently the canonical double-commutator localization correction vanishes, and the
symmetrized/conventional current reduces to `q v`.

This is a theorem about the canonical corrected representative.  It does not remove arbitrary full
current-extension data away from exact differentials.
-/

namespace QuantumMechanics
namespace SingleParticle

variable {Test OneForm : Type*}
variable [AddCommGroup Test] [Module ℂ Test]
variable [AddCommGroup OneForm] [Module ℂ OneForm]
variable (V : Type*) [AddCommGroup V] [Module ℂ V]

/-- The localization correction vanishes identically for a scalar multiple of the identity. -/
@[simp]
theorem localizationCorrectionFlux_smul_id_eq_zero
    (velocity : V →ₗ[ℂ] V)
    (N : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V))
    (q : ℂ) :
    localizationCorrectionFlux V velocity (q • LinearMap.id) N = 0 := by
  apply localizationCorrectionFlux_eq_zero_of_commutes V velocity (q • LinearMap.id) N
  intro α
  exact _root_.ConservationLaw.linearCommutator_smul_id_right (N α) q

/-- The symmetrized/conventional flux for a scalar charge quantity is the local pairing with
`q • velocity`. -/
theorem symmetrizedVelocityCurrentFlux_smul_id
    (velocity : V →ₗ[ℂ] V)
    (N : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V))
    (q : ℂ) :
    symmetrizedVelocityCurrentFlux V velocity (q • LinearMap.id) N =
      operatorLocalCurrentPairing V N (q • velocity) := by
  change operatorLocalCurrentPairing V N
      (symmetrizedVelocityCurrent V velocity (q • LinearMap.id)) =
    operatorLocalCurrentPairing V N (q • velocity)
  rw [symmetrizedVelocityCurrent_smul_id]

/-- The canonical corrected current functional for a charge-like quantity has no correction and is
represented by the conventional density `q v`. -/
theorem correctedChargeCurrentFlux_eq
    (velocity : V →ₗ[ℂ] V)
    (N : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V))
    (q : ℂ) :
    symmetrizedVelocityCurrentFlux V velocity (q • LinearMap.id) N +
        localizationCorrectionFlux V velocity (q • LinearMap.id) N =
      operatorLocalCurrentPairing V N (q • velocity) := by
  rw [localizationCorrectionFlux_smul_id_eq_zero]
  simp [symmetrizedVelocityCurrentFlux_smul_id]

/-- The chosen corrected differential-current representation itself reduces to the charge-current
pairing `q v` when the transported quantity is `q I`. -/
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
    symmetrizedVelocityCurrentFlux V velocity (q • LinearMap.id) N +
        localizationCorrectionFlux V velocity (q • LinearMap.id) N =
      operatorLocalCurrentPairing V N (q • velocity)
  exact correctedChargeCurrentFlux_eq V velocity N q

end SingleParticle
end QuantumMechanics
