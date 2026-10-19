import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.Bounded
import LeanCondensedMatter.QuantumTheory.LinearResponse.RetardedSusceptibility

set_option linter.style.header false

/-!
# Flux response without a chosen current representation

This module connects a one-body test-space flux functional directly to the observable-generic
retarded Kubo kernel.  The fundamental input is

```text
Φ : Test → one-body operator,
```

not a chosen current-density convention.  A differential current representation
`Φ f = J (d f)` is consumed only as a downstream representation theorem.

Flux here denotes the term in a balance law, not an intrinsic Hall mechanism.
The distinction between exact flux and an arbitrary/global current component is kept explicit:
`DifferentialCurrentEquivalent` guarantees agreement only on one-forms of the form `d f`.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open _root_.SecondQuantization.Fermionic.Lattice

noncomputable section

variable {Site Test : Type*}
variable [LinearOrder Site] [Fintype Site]
variable [AddCommGroup Test] [Module ℂ Test]

/-- Retarded Kubo response of an intrinsic one-body flux, linear in the test object. -/
noncomputable def boundedFluxRetardedResponse
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (source : FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (Φ : Test →ₗ[ℂ] ((Site →₀ ℂ) →ₗ[ℂ] (Site →₀ ℂ)))
    (t s : ℝ) : Test →ₗ[ℂ] ℂ :=
  (QuantumTheory.LinearResponse.retardedSusceptibilityMeasuredLinearMap
      system expectation source t s).comp
    ((boundedOneBodyOperatorLinearMap (Site := Site)).comp Φ)

end
end Transport
end Fermionic
end SecondQuantization
