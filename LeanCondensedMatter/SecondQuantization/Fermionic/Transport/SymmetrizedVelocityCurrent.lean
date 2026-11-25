import LeanCondensedMatter.QuantumTheory.ConservationLaw.HeisenbergEvolution
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

attribute [local instance 100] LieRing.ofAssociativeRing

open _root_.SecondQuantization.Fermionic.Lattice
open QuantumTheory.ConservationLaw

noncomputable section

variable {Site : Type*} [LinearOrder Site] [Fintype Site]

/-- With velocity fixed, bounded second-quantized symmetrized current is complex-linear in the
transported one-body quantity. -/
noncomputable def boundedSymmetrizedVelocityCurrentLinear
    (velocity : (Site →₀ ℂ) →ₗ[ℂ] (Site →₀ ℂ)) :
    ((Site →₀ ℂ) →ₗ[ℂ] (Site →₀ ℂ)) →ₗ[ℂ]
      (FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site) :=
  (boundedOneBodyOperator (Site := Site)).toLinearMap.comp
    (_root_.LinearMap.symmetrizedProductBilinear (K := ℂ) ((Site →₀ ℂ) →ₗ[ℂ] (Site →₀ ℂ)) velocity)


/-- The derivative of a symmetrically localized one-body quantity lifts to
the conventional velocity current plus the position-weighted source term.
The symmetric product is formed before second quantization; no multiplicative
property of the one-body Fock lift is assumed. -/
theorem boundedHeisenbergSymmetrizedProduct_eq
    (hbar : ℝ) (H X m : (Site →₀ ℂ) →ₗ[ℂ] (Site →₀ ℂ)) :
    boundedOneBodyOperator
        (heisenbergEvolution hbar H
          (LinearMap.symmetrizedProduct (K := ℂ) X m)) =
      boundedSymmetrizedVelocityCurrentLinear
          (heisenbergEvolution hbar H X) m +
        boundedSymmetrizedVelocityCurrentLinear X
          (heisenbergEvolution hbar H m) := by
  rw [heisenbergEvolution_symmetrizedProduct]
  exact map_add (boundedOneBodyOperator (Site := Site)).toLinearMap _ _

end
end Transport
end Fermionic
end SecondQuantization
