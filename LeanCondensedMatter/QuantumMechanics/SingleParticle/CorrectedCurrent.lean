import LeanCondensedMatter.Analysis.ConservationLaw.CorrectedCurrentFlux
import LeanCondensedMatter.Analysis.ConservationLaw.CurrentEquivalence
import LeanCondensedMatter.QuantumMechanics.SingleParticle.IntrinsicLocalizedTransport

set_option linter.style.header false

/-!
# Corrected symmetrized-velocity current

For a general transported one-body quantity `m`, the intrinsic localized transport need not be
represented by the symmetrized velocity current `1/2 {v,m}` alone. The representation-independent
operator algebra is owned by `Analysis.ConservationLaw.CorrectedCurrentFlux`:

```text
J_nested = J_sym + J_corr
J_corr(α) = 1/4 [v,[N α,m]].
```

This module supplies only the one-particle quantum-mechanical bridge: when Heisenberg evolution of
the localizer is represented by a distinguished velocity, the generic nested flux represents the
intrinsic Heisenberg transport. No duplicate current-flux algebra is defined here.
-/

namespace QuantumMechanics
namespace SingleParticle

variable {Test OneForm : Type*}
variable [AddCommGroup Test] [Module ℂ Test]
variable [AddCommGroup OneForm] [Module ℂ OneForm]
variable (V : Type*) [AddCommGroup V] [Module ℂ V]

/-- A velocity representation of localizer evolution lifts to the generic nested current flux for
an arbitrary transported operator `m`; no locality/commutation assumption on `m` is needed. -/
theorem factorsThroughDifferential_nestedSymmetrizedCurrentFlux
    (ℏ : ℝ) (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m velocity : V →ₗ[ℂ] V)
    (d : Test →ₗ[ℂ] OneForm)
    (N : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V))
    (hvelocity : _root_.ConservationLaw.FactorsThroughDifferential d
      (heisenbergLocalizationFunctional V ℏ h M)
      (velocityLocalizationFlux V velocity N)) :
    _root_.ConservationLaw.FactorsThroughDifferential d
      (heisenbergTransportFunctional V ℏ h M m)
      (_root_.ConservationLaw.nestedSymmetrizedCurrentFlux V velocity m N) := by
  rw [heisenbergTransportFunctional_eq_symmetrizedProductRight_comp V ℏ h M m]
  simpa [_root_.ConservationLaw.nestedSymmetrizedCurrentFlux, velocityLocalizationFlux] using
    (_root_.ConservationLaw.FactorsThroughDifferential.postcomp hvelocity
      (_root_.ConservationLaw.symmetrizedProductRightLinear V m))

/-- The generic nested current flux is a chosen full differential-current representation of the
intrinsic transport whenever the localized Heisenberg evolution has a velocity representation. -/
noncomputable def correctedSymmetrizedVelocityCurrentRepresentation
    (ℏ : ℝ) (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m velocity : V →ₗ[ℂ] V)
    (d : Test →ₗ[ℂ] OneForm)
    (N : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V))
    (hvelocity : _root_.ConservationLaw.FactorsThroughDifferential d
      (heisenbergLocalizationFunctional V ℏ h M)
      (velocityLocalizationFlux V velocity N)) :
    _root_.ConservationLaw.DifferentialCurrentRepresentation d
      (heisenbergTransportFunctional V ℏ h M m) where
  current := _root_.ConservationLaw.nestedSymmetrizedCurrentFlux V velocity m N
  factors := factorsThroughDifferential_nestedSymmetrizedCurrentFlux
    V ℏ h M m velocity d N hvelocity

/-- Any other full current functional representing the same intrinsic transport is equivalent on
exact differentials to the generic nested current flux. -/
theorem currentEquivalent_nestedSymmetrizedCurrentFlux
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
    _root_.ConservationLaw.DifferentialCurrentEquivalent d R.current
      (_root_.ConservationLaw.nestedSymmetrizedCurrentFlux V velocity m N) :=
  R.currentEquivalent
    (correctedSymmetrizedVelocityCurrentRepresentation
      V ℏ h M m velocity d N hvelocity)

end SingleParticle
end QuantumMechanics
