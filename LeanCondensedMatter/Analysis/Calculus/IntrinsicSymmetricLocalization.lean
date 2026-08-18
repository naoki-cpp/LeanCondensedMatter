import LeanCondensedMatter.Analysis.Calculus.IntrinsicBalanceLaw
import LeanCondensedMatter.Analysis.Calculus.SymmetricLocalization

set_option linter.style.header false

/-!
# Intrinsic symmetric-localization balance law

This module packages symmetric localization into `IntrinsicBalanceLaw` without choosing a full
current functional on all one-form-like test data.

The required input is only that the transport functional depends on the differential `d f`.  A
factorization `transport = J ∘ d` remains a sufficient way to prove that dependence, but the chosen
extension `J : OneForm → Obs` is not stored in the intrinsic balance law.
-/

namespace ConservationLaw

variable {Test OneForm : Type*}
variable [AddCommGroup Test] [Module ℂ Test]
variable [AddCommGroup OneForm] [Module ℂ OneForm]
variable (V : Type*) [AddCommGroup V] [Module ℂ V]

/-- Symmetric localization gives an intrinsic balance law as soon as its transport depends only on
differential test data. -/
noncomputable def intrinsicSymmetricLocalizationBalanceLaw
    (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m : V →ₗ[ℂ] V)
    (d : Test →ₗ[ℂ] OneForm)
    (htransport : DependsOnlyOnDifferential d (transportFunctional V h M m)) :
    IntrinsicBalanceLaw
      (commutatorEvolution h)
      (localizedQuantityFunctional V M m)
      d where
  transport := transportFunctional V h M m
  transport_depends := htransport
  source := sourceFunctional V h M m
  balance := by
    intro f
    simpa using commutatorEvolution_localizedQuantityFunctional V h M m f

/-- A conventional differential-current factorization is sufficient to construct the intrinsic
symmetric-localization balance law, but the representing current is forgotten afterwards. -/
noncomputable def intrinsicSymmetricLocalizationBalanceLawOfFactors
    (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m : V →ₗ[ℂ] V)
    (d : Test →ₗ[ℂ] OneForm)
    (J : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V))
    (hJ : FactorsThroughDifferential d (transportFunctional V h M m) J) :
    IntrinsicBalanceLaw
      (commutatorEvolution h)
      (localizedQuantityFunctional V M m)
      d :=
  intrinsicSymmetricLocalizationBalanceLaw V h M m d
    (DependsOnlyOnDifferential.of_factors hJ)

end ConservationLaw
