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

/-- Mixed charge-current response channel: independent measured and Peierls-source
directions, with the contact fixed by the mixed Peierls derivative. -/
noncomputable def boundedMixedDirectionalResponseChannel
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (geometry : LatticeGeometry Site E) (measured source : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q : ℝ) :
    QuantumTheory.LinearResponse.ResponseChannel (FiniteLatticeHilbertFock Site) where
  measured := boundedDirectionalCurrent geometry measured
    (system.hbar : ℂ) (q : ℂ) K
  source := boundedDirectionalCurrent geometry source
    (system.hbar : ℂ) (q : ℂ) K
  observableVariation := boundedMixedDirectionalContact geometry measured source
    (system.hbar : ℂ) (q : ℂ) K

/-- The existing directional channel is the diagonal mixed channel. -/
noncomputable def boundedDirectionalResponseChannel
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q : ℝ) :
    QuantumTheory.LinearResponse.ResponseChannel (FiniteLatticeHilbertFock Site) :=
  boundedMixedDirectionalResponseChannel system geometry direction direction K q

end
end Transport
end Fermionic
end SecondQuantization
