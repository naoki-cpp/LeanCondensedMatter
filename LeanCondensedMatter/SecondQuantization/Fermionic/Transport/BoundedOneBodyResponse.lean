import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.Bounded
import LeanCondensedMatter.QuantumTheory.LinearResponse.MeasuredObservableLinearity

set_option linter.style.header false

/-!
# Generic bounded one-body response adapter

The finite-lattice realization of an arbitrary one-body operator as a bounded Fock-space observable
is owned by `Fermionic.Lattice.Bounded`. This module composes that representation bridge with the
observable-generic Kubo API.

No current-density convention is assumed. Current-specific response wrappers may specialize this
neutral adapter downstream.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open _root_.SecondQuantization.Fermionic.Lattice

noncomputable section

variable {Site : Type*} [LinearOrder Site] [Fintype Site]

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
