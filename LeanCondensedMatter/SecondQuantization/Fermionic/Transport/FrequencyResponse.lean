import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.GeometricCurrent
import LeanCondensedMatter.QuantumTheory.LinearResponse.FiniteTimeAdiabatic

set_option linter.style.header false

/-!
# Finite-time fermionic directional frequency response

This module constructs the physical directional-current response channel of a finite fermionic
lattice for the generic finite-time and stationary-response interfaces. The response combines the
continuity-derived directional current with the explicit Peierls contact contribution.

For a source proportional to

```text
exp (η t) exp (-i ω t),
```

factoring out its value at the observation time leaves the canonical linear-response lag phase

```text
exp ((-η + i ω) τ).
```

No infinite-observation-time, zero-switching, DC, or thermodynamic limit is asserted here.
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
