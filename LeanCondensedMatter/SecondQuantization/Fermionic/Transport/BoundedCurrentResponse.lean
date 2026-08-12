import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.Bounded
import LeanCondensedMatter.QuantumTheory.LinearResponse.RetardedSusceptibility

set_option linter.style.header false

/-!
# Finite-lattice bond-current response adapter

This module is intentionally downstream of `Fermionic.Lattice`. It contains only the generic
linear-response wrapper for bounded lattice currents; the finite-lattice model realization itself
is owned by `Fermionic.Lattice.Bounded`.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open Lattice

noncomputable section

variable {Site : Type*} [LinearOrder Site] [Fintype Site]

/-- The bounded current-current retarded kernel supplied to the general Kubo API.

This is the causal commutator contribution for two derived bond currents. It is deliberately not
named conductivity: a vector-potential response must also account for explicit source dependence of
the measured current, as developed downstream in issue #444. -/
noncomputable def boundedBondCurrentRetardedSusceptibility
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (ℏ q : ℂ) (K : LocallyFiniteHopping Site)
    (x y u v : Site) (t s : ℝ) : ℂ :=
  QuantumTheory.LinearResponse.retardedSusceptibility system expectation
    (boundedBondCurrent ℏ q K x y)
    (boundedBondCurrent ℏ q K u v) t s


end
end Transport
end Fermionic
end SecondQuantization
