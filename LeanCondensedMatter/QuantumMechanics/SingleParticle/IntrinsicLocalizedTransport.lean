import LeanCondensedMatter.Analysis.Calculus.IntrinsicBalanceLaw
import LeanCondensedMatter.QuantumMechanics.SingleParticle.LocalizedTransport

set_option linter.style.header false

/-!
# Intrinsic one-particle localized transport

This module makes the intrinsic transport functional primary in the first-quantized Heisenberg
specialization.  A full current functional on all one-form-like test data is not required to state
the balance law; such a current is downstream representation data.
-/

namespace QuantumMechanics
namespace SingleParticle

open QuantumTheory.ConservationLaw

variable {Test OneForm : Type*}
variable [AddCommGroup Test] [Module ℂ Test]
variable [AddCommGroup OneForm] [Module ℂ OneForm]
variable (V : Type*) [AddCommGroup V] [Module ℂ V]

/-- Heisenberg evolution of a symmetrically localized one-body quantity gives an intrinsic balance
law as soon as its transport functional depends only on differential test data. -/
noncomputable def heisenbergIntrinsicSymmetricLocalizationBalanceLaw
    (ℏ : ℝ) (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m : V →ₗ[ℂ] V)
    (d : Test →ₗ[ℂ] OneForm)
    (htransport : _root_.ConservationLaw.DependsOnlyOnDifferential d
      (heisenbergTransportFunctional V ℏ h M m)) :
    _root_.ConservationLaw.IntrinsicBalanceLaw
      (heisenbergEvolution V ℏ h)
      (_root_.ConservationLaw.localizedQuantityFunctional V M m)
      d where
  transport := heisenbergTransportFunctional V ℏ h M m
  transport_depends := htransport
  source := heisenbergSourceFunctional V ℏ h M m
  balance := by
    intro f
    change heisenbergScale ℏ •
        _root_.ConservationLaw.linearCommutator h
          (_root_.ConservationLaw.localizedQuantity V M m f) = _
    rw [_root_.ConservationLaw.linearCommutator_localizedQuantity]
    simp [heisenbergSourceFunctional, heisenbergTransportFunctional, smul_add]

/-- A chosen differential-current factorization is sufficient to construct the intrinsic
Heisenberg balance law, but the chosen extension is forgotten. -/
noncomputable def heisenbergIntrinsicSymmetricLocalizationBalanceLawOfFactors
    (ℏ : ℝ) (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m : V →ₗ[ℂ] V)
    (d : Test →ₗ[ℂ] OneForm)
    (J : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V))
    (hJ : _root_.ConservationLaw.FactorsThroughDifferential d
      (heisenbergTransportFunctional V ℏ h M m) J) :
    _root_.ConservationLaw.IntrinsicBalanceLaw
      (heisenbergEvolution V ℏ h)
      (_root_.ConservationLaw.localizedQuantityFunctional V M m)
      d :=
  heisenbergIntrinsicSymmetricLocalizationBalanceLaw V ℏ h M m d
    (_root_.ConservationLaw.DependsOnlyOnDifferential.of_factors hJ)

/-- Recover the represented balance law only after choosing a current extension of the intrinsic
transport. -/
noncomputable def heisenbergRepresentedBalanceLawOfIntrinsic
    (ℏ : ℝ) (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m : V →ₗ[ℂ] V)
    (d : Test →ₗ[ℂ] OneForm)
    (J : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V))
    (hJ : _root_.ConservationLaw.FactorsThroughDifferential d
      (heisenbergTransportFunctional V ℏ h M m) J) :
    _root_.ConservationLaw.BalanceLaw
      (heisenbergEvolution V ℏ h)
      (_root_.ConservationLaw.localizedQuantityFunctional V M m)
      d :=
  (heisenbergIntrinsicSymmetricLocalizationBalanceLawOfFactors V ℏ h M m d J hJ).toRepresented
    J hJ

end SingleParticle
end QuantumMechanics
