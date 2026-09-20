import LeanCondensedMatter.Analysis.Calculus.BalanceLaw
import LeanCondensedMatter.Analysis.Calculus.SymmetricLocalizationAlgebra

set_option linter.style.header false

/-!
# Represented symmetric-localization balance law

This module packages the shared symmetric-localization operator decomposition into a represented
`BalanceLaw` after choosing a current extension on all one-form-like test data.  The underlying
commutator and localization algebra is owned by `SymmetricLocalizationAlgebra`.
-/

namespace ConservationLaw

variable {Test OneForm : Type*}
variable [AddCommGroup Test] [Module ℂ Test]
variable [AddCommGroup OneForm] [Module ℂ OneForm]
variable (V : Type*) [AddCommGroup V] [Module ℂ V]

/-- The symmetric-localization commutator decomposition becomes an abstract balance law whenever
the transport term has a differential current representation. -/
noncomputable def symmetricLocalizationBalanceLaw
    (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m : V →ₗ[ℂ] V)
    (d : Test →ₗ[ℂ] OneForm)
    (J : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V))
    (hJ : FactorsThroughDifferential d (transportFunctional V h M m) J) :
    BalanceLaw (commutatorEvolution h) (localizedQuantityFunctional V M m) d where
  current := J
  source := sourceFunctional V h M m
  balance := by
    intro f
    rw [commutatorEvolution_localizedQuantityFunctional V h M m f, hJ f]

end ConservationLaw
