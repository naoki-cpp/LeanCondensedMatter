import LeanCondensedMatter.Analysis.Operator.SymmetrizedProduct
import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.BoundedOneBodyResponse

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

The neutral `BoundedOneBodyResponse` layer remains independent of current conventions.
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
    (velocity : LatticeState Site →ₗ[ℂ] LatticeState Site) :
    (LatticeState Site →ₗ[ℂ] LatticeState Site) →ₗ[ℂ]
      (FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site) :=
  (boundedOneBodyOperatorLinearMap (Site := Site)).comp
    (_root_.ConservationLaw.symmetrizedProductLeftLinear (LatticeState Site) velocity)

/-- Bounded many-body realization of the generic symmetrized velocity current
`jᵐ = 1/2 {v,m}`. -/
noncomputable def boundedSymmetrizedVelocityCurrent
    (velocity m : LatticeState Site →ₗ[ℂ] LatticeState Site) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  boundedSymmetrizedVelocityCurrentLinear velocity m

@[simp]
theorem boundedSymmetrizedVelocityCurrentLinear_apply
    (velocity m : LatticeState Site →ₗ[ℂ] LatticeState Site) :
    boundedSymmetrizedVelocityCurrentLinear velocity m =
      boundedSymmetrizedVelocityCurrent velocity m :=
  rfl

end
end Transport
end Fermionic
end SecondQuantization
