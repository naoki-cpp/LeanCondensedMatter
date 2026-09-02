import LeanCondensedMatter.Analysis.Calculus.CurrentEquivalence
import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.BoundedOneBodyResponse

set_option linter.style.header false

/-!
# Intrinsic-flux response adapter

This module connects a one-body intrinsic transport functional directly to the observable-generic
retarded Kubo kernel.  The fundamental input is

```text
Φ : Test → one-body operator,
```

not a chosen current-density convention.  A differential current representation
`Φ f = J (d f)` is consumed only as a downstream representation theorem.

The distinction between exact flux and an arbitrary/global current component is kept explicit:
`DifferentialCurrentEquivalent` guarantees agreement only on one-forms of the form `d f`.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open _root_.SecondQuantization.Fermionic.Lattice

noncomputable section

variable {Site Test OneForm : Type*}
variable [LinearOrder Site] [Fintype Site]
variable [AddCommGroup Test] [Module ℂ Test]
variable [AddCommGroup OneForm] [Module ℂ OneForm]

/-- Bounded Fock-space realization of a one-body intrinsic flux functional. -/
noncomputable def boundedIntrinsicFlux
    (Φ : Test →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site)) :
    Test →ₗ[ℂ]
      (FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site) :=
  (boundedOneBodyOperatorLinearMap (Site := Site)).comp Φ

/-- Retarded Kubo response of an intrinsic one-body flux, linear in the test object. -/
noncomputable def boundedIntrinsicFluxRetardedResponse
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (source : FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (Φ : Test →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (t s : ℝ) : Test →ₗ[ℂ] ℂ :=
  (boundedOneBodyRetardedResponseLinearMap system expectation source t s).comp Φ

/-- Retarded response associated with one chosen full current functional on one-form-like data.
This API deliberately remains distinct from `boundedIntrinsicFluxRetardedResponse`: away from
`range d`, the current functional contains extension data not fixed by the intrinsic balance law. -/
noncomputable def boundedCurrentFunctionalRetardedResponse
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (source : FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (J : OneForm →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (t s : ℝ) : OneForm →ₗ[ℂ] ℂ :=
  boundedIntrinsicFluxRetardedResponse system expectation source J t s

/-- A differential-current representation produces exactly the same bounded observable on every
exact flux test. -/
theorem boundedIntrinsicFlux_eq_currentRepresentation
    (d : Test →ₗ[ℂ] OneForm)
    (Φ : Test →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (R : _root_.ConservationLaw.DifferentialCurrentRepresentation d Φ)
    (f : Test) :
    boundedIntrinsicFlux Φ f = boundedOneBodyOperator (R.current (d f)) := by
  change boundedOneBodyOperator (Φ f) = boundedOneBodyOperator (R.current (d f))
  rw [R.factors f]

/-- The intrinsic-flux Kubo response agrees with any chosen differential-current representation on
exact differential data. -/
theorem boundedIntrinsicFluxRetardedResponse_eq_currentRepresentation
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (source : FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (d : Test →ₗ[ℂ] OneForm)
    (Φ : Test →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (R : _root_.ConservationLaw.DifferentialCurrentRepresentation d Φ)
    (t s : ℝ) (f : Test) :
    boundedIntrinsicFluxRetardedResponse system expectation source Φ t s f =
      boundedCurrentFunctionalRetardedResponse system expectation source R.current t s (d f) := by
  change
    boundedOneBodyRetardedResponseLinearMap system expectation source t s (Φ f) =
      boundedOneBodyRetardedResponseLinearMap system expectation source t s (R.current (d f))
  rw [R.factors f]

/-- Equivalent full current functionals give the same retarded response on every exact
differential.  No statement is made here for an arbitrary non-exact one-form. -/
theorem boundedCurrentFunctionalRetardedResponse_eq_of_differentialEquivalent
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (source : FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (d : Test →ₗ[ℂ] OneForm)
    (J₁ J₂ : OneForm →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (hJ : _root_.ConservationLaw.DifferentialCurrentEquivalent d J₁ J₂)
    (t s : ℝ) (f : Test) :
    boundedCurrentFunctionalRetardedResponse system expectation source J₁ t s (d f) =
      boundedCurrentFunctionalRetardedResponse system expectation source J₂ t s (d f) := by
  change
    boundedOneBodyRetardedResponseLinearMap system expectation source t s (J₁ (d f)) =
      boundedOneBodyRetardedResponseLinearMap system expectation source t s (J₂ (d f))
  rw [hJ f]

/-- A chosen global current component agrees with the intrinsic response once it is explicitly
identified as an exact differential.  This witness is essential: exact-differential equivalence
alone does not identify arbitrary/global one-forms. -/
theorem boundedCurrentFunctionalRetardedResponse_eq_intrinsic_of_eq_differential
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (source : FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (d : Test →ₗ[ℂ] OneForm)
    (Φ : Test →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (R : _root_.ConservationLaw.DifferentialCurrentRepresentation d Φ)
    (t s : ℝ) (α : OneForm) (f : Test) (hα : α = d f) :
    boundedCurrentFunctionalRetardedResponse system expectation source R.current t s α =
      boundedIntrinsicFluxRetardedResponse system expectation source Φ t s f := by
  subst α
  exact (boundedIntrinsicFluxRetardedResponse_eq_currentRepresentation
    system expectation source d Φ R t s f).symm

end
end Transport
end Fermionic
end SecondQuantization
