import LeanCondensedMatter.Analysis.ConservationLaw.CurrentEquivalence
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

/-- A differential-current representation identifies the intrinsic Kubo response with
the chosen current response precomposed by the differential. The equality is only on exact
differentials; no equality of arbitrary current extensions is implied. -/
theorem boundedIntrinsicFluxRetardedResponse_eq_comp_of_isDifferentialCurrent
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (source : FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (d : Test →ₗ[ℂ] OneForm)
    (Φ : Test →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (J : OneForm →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (hΦ : _root_.ConservationLaw.IsDifferentialCurrent d Φ J)
    (t s : ℝ) :
    boundedIntrinsicFluxRetardedResponse system expectation source Φ t s =
      (boundedIntrinsicFluxRetardedResponse system expectation source J t s).comp d := by
  apply LinearMap.ext
  intro f
  change
    boundedOneBodyRetardedResponseLinearMap system expectation source t s (Φ f) =
      boundedOneBodyRetardedResponseLinearMap system expectation source t s (J (d f))
  rw [hΦ f]

/-- Equivalent full current functionals give the same retarded response on every exact
differential.  No statement is made here for an arbitrary non-exact one-form. -/
theorem boundedIntrinsicFluxRetardedResponse_eq_of_differentialEquivalent
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (source : FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (d : Test →ₗ[ℂ] OneForm)
    (J₁ J₂ : OneForm →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (hJ : _root_.ConservationLaw.DifferentialCurrentEquivalent d J₁ J₂)
    (t s : ℝ) (f : Test) :
    boundedIntrinsicFluxRetardedResponse system expectation source J₁ t s (d f) =
      boundedIntrinsicFluxRetardedResponse system expectation source J₂ t s (d f) := by
  change
    boundedOneBodyRetardedResponseLinearMap system expectation source t s (J₁ (d f)) =
      boundedOneBodyRetardedResponseLinearMap system expectation source t s (J₂ (d f))
  rw [hJ f]

/-- A chosen global current component agrees with the intrinsic response once it is explicitly
identified as an exact differential.  This witness is essential: exact-differential equivalence
alone does not identify arbitrary/global one-forms. -/
theorem boundedIntrinsicFluxRetardedResponse_current_eq_of_eq_differential
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (source : FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (d : Test →ₗ[ℂ] OneForm)
    (Φ : Test →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (R : _root_.ConservationLaw.DifferentialCurrentRepresentation d Φ)
    (t s : ℝ) (α : OneForm) (f : Test) (hα : α = d f) :
    boundedIntrinsicFluxRetardedResponse system expectation source R.current t s α =
      boundedIntrinsicFluxRetardedResponse system expectation source Φ t s f := by
  subst α
  exact (congrArg (fun response : Test →ₗ[ℂ] ℂ => response f)
    (boundedIntrinsicFluxRetardedResponse_eq_comp_of_isDifferentialCurrent
      system expectation source d Φ R.current R.isCurrent t s)).symm

end
end Transport
end Fermionic
end SecondQuantization
