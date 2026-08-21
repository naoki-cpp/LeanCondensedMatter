import LeanCondensedMatter.Analysis.Operator.SymmetrizedProduct
import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.BoundedOneBodyResponse

set_option linter.style.header false

/-!
# Bounded conventional-current adapter

This module specializes the generic bounded one-body operator boundary to the conventional current

```text
jᵐ = 1/2 {v,m}.
```

The neutral `BoundedOneBodyResponse` module intentionally does not depend on any current-density
representation. At this layer the supplied one-body operators `v` and `m` are combined only through
the shared analysis-level symmetrized product; the concrete first-quantized velocity interpretation
remains in `QuantumMechanics.SingleParticle`.

Response consumers should pass `boundedConventionalCurrent` directly to the observable-generic Kubo
API rather than introducing another conventional-current-specific response wrapper.
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

end
end Transport
end Fermionic
end SecondQuantization
