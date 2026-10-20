import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.GeometricCurrent
import LeanCondensedMatter.QuantumTheory.LinearResponse.Dynamics.Free
import LeanCondensedMatter.QuantumTheory.LinearResponse.Response.Channel

set_option linter.style.header false

/-!
# Fermionic charge-current response channel

This module packages the continuity-derived charge current and the Peierls contact variation
of a finite fermionic lattice as a general response channel. It performs no time integration or
frequency transformation. Consumers supply the dynamics and expectation to the general response
operations, and attach physical volume and electric-field normalization separately.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open _root_.SecondQuantization.Fermionic.Lattice
open QuantumTheory.LinearResponse

noncomputable section

variable {Site E : Type*}
variable [LinearOrder Site] [Fintype Site]
variable [AddCommGroup E] [Module ℝ E]

/-- Neutral response channel for the finite-lattice directional charge current.

The measured and source operators are the same directional current, while the explicit first-order
observable variation is the Peierls contact operator. -/
noncomputable def boundedDirectionalResponseChannel
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q : ℝ) :
    QuantumTheory.LinearResponse.ResponseChannel (FiniteLatticeHilbertFock Site) where
  measured := boundedDirectionalCurrent geometry direction
    (system.hbar : ℂ) (q : ℂ) K
  source := boundedDirectionalCurrent geometry direction
    (system.hbar : ℂ) (q : ℂ) K
  observableVariation := boundedDirectionalContact geometry direction
    (system.hbar : ℂ) (q : ℂ) K

end
end Transport
end Fermionic
end SecondQuantization
