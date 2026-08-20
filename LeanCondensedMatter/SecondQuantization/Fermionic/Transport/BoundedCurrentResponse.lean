import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.Bounded
import LeanCondensedMatter.QuantumTheory.LinearResponse.RetardedSusceptibility

set_option linter.style.header false

/-!
# Bounded generalized-current response adapters

This module is the generic finite-lattice bridge from supplied one-particle current operators to the
observable-generic Kubo API. It depends on the bounded lattice realization, but not on any particular
current-density representation such as the conventional current `1/2 {v,m}`.

A one-particle current operator `j` is transported by

```text
j  ↦  dΓ(j)  ↦  boundedLatticeOperator (dΓ(j)).
```

The measured current and the source-coupling observable remain separate inputs to the response.
Thus the primitive bounded adapter is `χᴿ_{J,B}`, not a hard-coded current-current correlator.
Charge, spin, orbital, and other concrete current representations should specialize the generic
one-body or measured-current API at their natural owner.

This module still does not call a retarded susceptibility a conductivity. If the measured observable
depends explicitly on the source, its observable-variation/contact term must be added by the
source-dependent response layer rather than hidden in the causal Kubo kernel.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open Lattice

noncomputable section

variable {Site : Type*} [LinearOrder Site] [Fintype Site]

/-- Bounded finite-lattice realization of a one-particle current operator.

The construction is basis-independent up to the already-proved lattice occupation equivalence:
first apply algebraic second quantization, then the canonical finite-lattice bounded transport. -/
noncomputable def boundedOneBodyCurrent
    (current : LatticeState Site →ₗ[ℂ] LatticeState Site) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  boundedLatticeOperator
    (AlgebraicFock.dGamma (LatticeState Site) current)

@[simp]
theorem boundedOneBodyCurrent_smul (c : ℂ)
    (current : LatticeState Site →ₗ[ℂ] LatticeState Site) :
    boundedOneBodyCurrent (c • current) = c • boundedOneBodyCurrent current := by
  change Lattice.boundedLatticeOperator
      (AlgebraicFock.dGamma (LatticeState Site) (c • current)) =
    c • Lattice.boundedLatticeOperator
      (AlgebraicFock.dGamma (LatticeState Site) current)
  rw [AlgebraicFock.dGamma_smul, Lattice.boundedLatticeOperator_smul]

/-- Generic bounded retarded response with a current as the measured observable and an independent
bounded source-coupling observable `B`.

For a scalar perturbation with the repository's convention `V(t) = -f(t) B`, this is the causal
kernel `χᴿ_{J,B}` supplied by the general Kubo theorem. -/
noncomputable def boundedMeasuredCurrentRetardedSusceptibility
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (measuredCurrent source :
      FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (t s : ℝ) : ℂ :=
  QuantumTheory.LinearResponse.retardedSusceptibility system expectation
    measuredCurrent source t s

/-- Kubo response of an arbitrary supplied one-particle current after `dΓ` and bounded finite-lattice
transport. No choice of charge, spin, or orbital current convention is imposed here. -/
noncomputable def boundedOneBodyCurrentRetardedSusceptibility
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (current : LatticeState Site →ₗ[ℂ] LatticeState Site)
    (source : FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (t s : ℝ) : ℂ :=
  boundedMeasuredCurrentRetardedSusceptibility system expectation
    (boundedOneBodyCurrent current) source t s

end
end Transport
end Fermionic
end SecondQuantization
