import LeanCondensedMatter.Analysis.Operator.SchwartzKinetic1D
import LeanCondensedMatter.QuantumMechanics.SingleParticle.SymmetrizedVelocityCurrent

set_option linter.style.header false

/-!
# Operator current representations for the one-dimensional Schwartz Schrödinger model

This module connects the analysis-only Schwartz localization identity to the generalized one-body
transport API. For

```text
H = -κ D² + M_V,
M_f ψ = f ψ,
v = -2 i κ D / ℏ,
```

the analysis layer proves

```text
(i/ℏ) [H, M_f] = 1/2 {M_(D f), v}.
```

For probability and charge the transported quantity is a scalar multiple of the identity, so it
commutes with multiplication localizers. The symmetrized velocity current therefore gives a local
current-density representation of the abstract transport functional.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

attribute [local instance 100] LieRing.ofAssociativeRing

open QuantumTheory.ConservationLaw

noncomputable section

/-- Complex Schwartz space used as the concrete one-particle space in this specialization. -/
abbrev SchwartzOneParticle1D := SchwartzKinetic1D.Space

/-- The velocity-generated localization flux is a differential current for the concrete Schwartz
Schrödinger localization transport. -/
theorem schwartzVelocityLocalizationFlux_isDifferentialCurrent1D
    (ℏ κ : ℝ) (potential : SchwartzOneParticle1D) :
    _root_.ConservationLaw.IsDifferentialCurrent
      SchwartzKinetic1D.derivative
      (heisenbergLocalizationFunctional SchwartzOneParticle1D ℏ
        (SchwartzKinetic1D.schrodingerOperator κ potential)
        SchwartzKinetic1D.multiplicationLinear)
      (velocityLocalizationFlux SchwartzOneParticle1D
        (SchwartzKinetic1D.velocityOperator ℏ κ)
        SchwartzKinetic1D.multiplicationLinear) := by
  intro f
  rw [heisenbergLocalizationFunctional_apply, velocityLocalizationFlux_apply]
  apply LinearMap.ext
  intro ψ
  have h := congrArg
    (fun T : SchwartzOneParticle1D →ₗ[ℂ] SchwartzOneParticle1D => T ψ)
    (SchwartzKinetic1D.heisenberg_localization_eq_symmetrized_velocity ℏ κ potential f)
  simpa [heisenbergScale, LieRing.of_associative_ring_bracket, Module.End.mul_eq_comp,
    _root_.ConservationLaw.symmetrizedProduct_apply] using h

/-- Probability transport (`m = I`) on the Schwartz Schrödinger model is locally represented by the
velocity operator itself. -/
noncomputable def schwartzOperatorProbabilityCurrentRepresentation1D
    (ℏ κ : ℝ) (potential : SchwartzOneParticle1D) :
    _root_.ConservationLaw.LocalCurrentDensityRepresentation
      SchwartzKinetic1D.derivative
      (heisenbergTransportFunctional SchwartzOneParticle1D ℏ
        (SchwartzKinetic1D.schrodingerOperator κ potential)
        SchwartzKinetic1D.multiplicationLinear LinearMap.id)
      (operatorLocalCurrentPairing SchwartzOneParticle1D
        SchwartzKinetic1D.multiplicationLinear) :=
  symmetrizedVelocityCurrentRepresentation SchwartzOneParticle1D ℏ
    (SchwartzKinetic1D.schrodingerOperator κ potential)
    SchwartzKinetic1D.multiplicationLinear
    LinearMap.id
    (SchwartzKinetic1D.velocityOperator ℏ κ)
    SchwartzKinetic1D.derivative
    SchwartzKinetic1D.multiplicationLinear
    (schwartzVelocityLocalizationFlux_isDifferentialCurrent1D ℏ κ potential)
    (fun α => by
      simp [LieRing.of_associative_ring_bracket, Module.End.mul_eq_comp])

@[simp]
theorem schwartzOperatorProbabilityCurrentRepresentation1D_currentDensity
    (ℏ κ : ℝ) (potential : SchwartzOneParticle1D) :
    (schwartzOperatorProbabilityCurrentRepresentation1D ℏ κ potential).currentDensity =
      SchwartzKinetic1D.velocityOperator ℏ κ := by
  change symmetrizedVelocityCurrent SchwartzOneParticle1D
      (SchwartzKinetic1D.velocityOperator ℏ κ) LinearMap.id = _
  exact symmetrizedVelocityCurrent_id SchwartzOneParticle1D
    (SchwartzKinetic1D.velocityOperator ℏ κ)

/-- Charge transport (`m = q I`) on the Schwartz Schrödinger model is locally represented by
`q v`. -/
noncomputable def schwartzOperatorChargeCurrentRepresentation1D
    (q : ℂ) (ℏ κ : ℝ) (potential : SchwartzOneParticle1D) :
    _root_.ConservationLaw.LocalCurrentDensityRepresentation
      SchwartzKinetic1D.derivative
      (heisenbergTransportFunctional SchwartzOneParticle1D ℏ
        (SchwartzKinetic1D.schrodingerOperator κ potential)
        SchwartzKinetic1D.multiplicationLinear (q • LinearMap.id))
      (operatorLocalCurrentPairing SchwartzOneParticle1D
        SchwartzKinetic1D.multiplicationLinear) :=
  symmetrizedVelocityCurrentRepresentation SchwartzOneParticle1D ℏ
    (SchwartzKinetic1D.schrodingerOperator κ potential)
    SchwartzKinetic1D.multiplicationLinear
    (q • LinearMap.id)
    (SchwartzKinetic1D.velocityOperator ℏ κ)
    SchwartzKinetic1D.derivative
    SchwartzKinetic1D.multiplicationLinear
    (schwartzVelocityLocalizationFlux_isDifferentialCurrent1D ℏ κ potential)
    (fun α => by
      simp [LieRing.of_associative_ring_bracket, Module.End.mul_eq_comp])

@[simp]
theorem schwartzOperatorChargeCurrentRepresentation1D_currentDensity
    (q : ℂ) (ℏ κ : ℝ) (potential : SchwartzOneParticle1D) :
    (schwartzOperatorChargeCurrentRepresentation1D q ℏ κ potential).currentDensity =
      q • SchwartzKinetic1D.velocityOperator ℏ κ := by
  change _root_.ConservationLaw.symmetrizedProduct
      (SchwartzKinetic1D.velocityOperator ℏ κ) (q • LinearMap.id) = _
  exact _root_.ConservationLaw.symmetrizedProduct_smul_id
    (SchwartzKinetic1D.velocityOperator ℏ κ) q

end
end Continuum
end SingleParticle
end QuantumMechanics
