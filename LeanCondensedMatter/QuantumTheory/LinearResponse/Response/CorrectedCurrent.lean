import LeanCondensedMatter.Analysis.ConservationLaw.SymmetricLocalizationAlgebra
import LeanCondensedMatter.QuantumTheory.LinearResponse.Response.Channel

set_option linter.style.header false

/-!
# Corrected current response

An arbitrary complex-linear realization of an algebra-valued current into bounded observables
suffices to lift the nested-flux decomposition into retarded response. In particular the
realization may be the identity or a bounded one-body Fock lift; multiplicativity and
preservation of commutators are not required.

The response decomposition holds on exact differential data, not on arbitrary extensions
of the current. The source and explicit observable variation remain independent channel data.
-/

namespace QuantumTheory
namespace LinearResponse

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : Type*} [Ring A] [Algebra ℂ A]
variable {Test OneForm : Type*}
variable [AddCommGroup Test] [Module ℂ Test]
variable [AddCommGroup OneForm] [Module ℂ OneForm]

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H)) (hbar : ℝ)
variable (realize : A →ₗ[ℂ] (H →L[ℂ] H))

/-- Retarded response of a realized flux, linear in the test object. -/
def fluxRetardedResponse
    (expectation : NormalizedExpectation H) (source : H →L[ℂ] H)
    (Φ : Test →ₗ[ℂ] A) (t s : ℝ) : Test →ₗ[ℂ] ℂ :=
  (retardedSusceptibilityMeasuredLinearMap U hbar expectation source t s).comp
    (realize.comp Φ)

/-- Response channel for a corrected current component with independent source and variation. -/
def correctedCurrentResponseChannel
    (velocity m : A) (N : OneForm →ₗ[ℂ] A) (α : OneForm)
    (source observableVariation : H →L[ℂ] H) : ResponseChannel H where
  measured := realize (_root_.ConservationLaw.nestedSymmetrizedCurrentFlux velocity m N α)
  source := source
  observableVariation := observableVariation

/-- On exact differentials the retarded flux response splits into symmetric and correction
contributions for any linear realization of the current. -/
theorem fluxRetardedResponse_eq_symmetrized_add_correction
    (expectation : NormalizedExpectation H) (source : H →L[ℂ] H)
    (d : Test →ₗ[ℂ] OneForm) (Φ : Test →ₗ[ℂ] A)
    (velocity m : A) (N : OneForm →ₗ[ℂ] A)
    (hΦ : Φ = (_root_.ConservationLaw.nestedSymmetrizedCurrentFlux velocity m N).comp d)
    (t s : ℝ) :
    fluxRetardedResponse U hbar realize expectation source Φ t s =
      (fluxRetardedResponse U hbar realize expectation source
        (_root_.ConservationLaw.symmetrizedCurrentFlux velocity m N) t s).comp d +
      (fluxRetardedResponse U hbar realize expectation source
        (_root_.ConservationLaw.localizationCorrectionCurrentFlux velocity m N) t s).comp d := by
  rw [hΦ, _root_.ConservationLaw.nestedSymmetrizedCurrentFlux_eq_symmetrized_add_correction]
  ext f
  simp only [fluxRetardedResponse, LinearMap.comp_apply, LinearMap.add_apply, map_add]

/-- Commuting localizers have no localization-correction response. -/
theorem fluxRetardedResponse_eq_symmetrized_of_commutes
    (expectation : NormalizedExpectation H) (source : H →L[ℂ] H)
    (d : Test →ₗ[ℂ] OneForm) (Φ : Test →ₗ[ℂ] A)
    (velocity m : A) (N : OneForm →ₗ[ℂ] A)
    (hΦ : Φ = (_root_.ConservationLaw.nestedSymmetrizedCurrentFlux velocity m N).comp d)
    (hcomm : ∀ α, ⁅N α, m⁆ = 0) (t s : ℝ) :
    fluxRetardedResponse U hbar realize expectation source Φ t s =
      (fluxRetardedResponse U hbar realize expectation source
        (_root_.ConservationLaw.symmetrizedCurrentFlux velocity m N) t s).comp d := by
  rw [fluxRetardedResponse_eq_symmetrized_add_correction
    U hbar realize expectation source d Φ velocity m N hΦ t s,
    _root_.ConservationLaw.localizationCorrectionCurrentFlux_eq_zero_of_commutes
      velocity m N hcomm]
  simp [fluxRetardedResponse]

/-- Scalar transported quantities have no localization-correction response. -/
theorem fluxRetardedResponse_eq_symmetrized_smul_one
    (expectation : NormalizedExpectation H) (source : H →L[ℂ] H)
    (d : Test →ₗ[ℂ] OneForm) (Φ : Test →ₗ[ℂ] A)
    (velocity : A) (N : OneForm →ₗ[ℂ] A) (q : ℂ)
    (hΦ : Φ = (_root_.ConservationLaw.nestedSymmetrizedCurrentFlux velocity (q • 1) N).comp d)
    (t s : ℝ) :
    fluxRetardedResponse U hbar realize expectation source Φ t s =
      (fluxRetardedResponse U hbar realize expectation source
        (_root_.ConservationLaw.symmetrizedCurrentFlux velocity (q • 1) N) t s).comp d := by
  rw [fluxRetardedResponse_eq_symmetrized_add_correction
    U hbar realize expectation source d Φ velocity (q • 1) N hΦ t s,
    _root_.ConservationLaw.localizationCorrectionCurrentFlux_smul_one]
  simp [fluxRetardedResponse]

end
end LinearResponse
end QuantumTheory
