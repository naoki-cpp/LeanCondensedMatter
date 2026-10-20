import LeanCondensedMatter.Analysis.Operator.SymmetrizedProduct
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.Bounded

set_option linter.style.header false

/-!
# Bounded symmetrized-velocity current

This module realizes the generic one-body current-density candidate

```text
jᵐ = 1/2 {v,m}
```

as a bounded finite-lattice Fock-space observable. The transported quantity `m` is arbitrary:
charge, spin, orbital angular momentum, and other one-body quantities are specializations at the
consumer.

The bounded one-body realization remains independent of current conventions.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open _root_.SecondQuantization.Fermionic.Lattice

noncomputable section

variable {Site : Type*} [LinearOrder Site] [Fintype Site]

/-- With velocity fixed, bounded second-quantized symmetrized current is complex-linear in the
transported one-body quantity. -/
noncomputable def boundedSymmetrizedVelocityCurrentLinear
    (velocity : (Site →₀ ℂ) →ₗ[ℂ] (Site →₀ ℂ)) :
    ((Site →₀ ℂ) →ₗ[ℂ] (Site →₀ ℂ)) →ₗ[ℂ]
      (FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site) :=
  (boundedOneBodyOperatorLinearMap (Site := Site)).comp
    (_root_.ConservationLaw.symmetrizedProductLeftLinear ((Site →₀ ℂ)) velocity)


end
end Transport
end Fermionic
end SecondQuantization
