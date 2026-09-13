import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.Bounded
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.SecondQuantizationLinearity
import LeanCondensedMatter.QuantumTheory.LinearResponse.MeasuredObservableLinearity

set_option linter.style.header false

/-!
# Generic bounded one-body response adapter

This module packages the finite-lattice map from an arbitrary one-body operator to the bounded
Fock-space observable consumed by the observable-generic Kubo API.  The construction is the linear
composition

```text
one-body operator
  -> dΓ
  -> bounded finite-lattice Fock operator.
```

No current-density convention is assumed.  Current-specific wrappers may specialize this neutral
operator bridge downstream.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open _root_.SecondQuantization.Fermionic.Lattice

noncomputable section

variable {Site : Type*} [LinearOrder Site] [Fintype Site]

/-- Linear finite-lattice realization of an arbitrary one-body operator as a bounded Fock-space
observable. -/
noncomputable def boundedOneBodyOperatorLinearMap :
    (LatticeState Site →ₗ[ℂ] LatticeState Site) →ₗ[ℂ]
      (FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site) :=
  (Lattice.boundedLatticeOperatorLinearMap (Site := Site)).comp
    (AlgebraicFock.dGammaLinear (LatticeState Site))

/-- Bounded Fock-space observable associated with one supplied one-body operator. -/
noncomputable def boundedOneBodyOperator
    (operator : LatticeState Site →ₗ[ℂ] LatticeState Site) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  boundedOneBodyOperatorLinearMap operator

/-- With system, state, source, and times fixed, the retarded response is a linear functional of the
supplied one-body measured operator. -/
noncomputable def boundedOneBodyRetardedResponseLinearMap
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (source : FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (t s : ℝ) :
    (LatticeState Site →ₗ[ℂ] LatticeState Site) →ₗ[ℂ] ℂ :=
  (QuantumTheory.LinearResponse.retardedSusceptibilityMeasuredLinearMap
      system expectation source t s).comp
    (boundedOneBodyOperatorLinearMap (Site := Site))

end
end Transport
end Fermionic
end SecondQuantization
