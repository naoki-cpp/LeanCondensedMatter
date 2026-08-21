import LeanCondensedMatter.Analysis.Operator.SymmetrizedProduct
import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.BoundedOneBodyResponse

set_option linter.style.header false

/-!
# Bounded conventional-current response adapters

This module specializes the generic bounded one-body response boundary to the conventional current

```text
jᵐ = 1/2 {v,m}.
```

The neutral `BoundedOneBodyResponse` module intentionally does not depend on any current-density
representation. At this layer the supplied one-body operators `v` and `m` are combined only through
the shared analysis-level symmetrized product; the concrete first-quantized velocity interpretation
remains in `QuantumMechanics.SingleParticle`.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open Lattice

noncomputable section

variable {Site : Type*} [LinearOrder Site] [Fintype Site]

/-- Bounded realization of the conventional generalized current `jᵐ = 1/2 {v,m}`. -/
noncomputable def boundedConventionalCurrent
    (velocity m : LatticeState Site →ₗ[ℂ] LatticeState Site) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  boundedOneBodyOperator
    (_root_.ConservationLaw.symmetrizedProduct velocity m)

/-- Kubo response of the conventional current `1/2 {v,m}` when that current representation has
been justified by the upstream generalized-balance-law hypotheses. -/
noncomputable def boundedConventionalCurrentRetardedSusceptibility
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (velocity m : LatticeState Site →ₗ[ℂ] LatticeState Site)
    (source : FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (t s : ℝ) : ℂ :=
  QuantumTheory.LinearResponse.retardedSusceptibility system expectation
    (boundedConventionalCurrent velocity m) source t s

end
end Transport
end Fermionic
end SecondQuantization
