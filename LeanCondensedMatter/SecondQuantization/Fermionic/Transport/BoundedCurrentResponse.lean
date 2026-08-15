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
The older bond-current/current-current wrapper is retained as a charge specialization, and the
one-particle bond operator recovers it by theorem.

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

/-- The one-particle operator underlying the existing oriented electric bond current is exactly a
special case of `boundedOneBodyCurrent`. -/
theorem boundedOneBodyCurrent_scaledBondOperator
    (ℏ q : ℂ) (K : LocallyFiniteHopping Site) (x y : Site) :
    boundedOneBodyCurrent (((Complex.I * q) / ℏ) • K.bondOperator x y) =
      boundedBondCurrent ℏ q K x y := by
  change Lattice.boundedLatticeOperator
      (AlgebraicFock.dGamma (LatticeState Site)
        (((Complex.I * q) / ℏ) • K.bondOperator x y)) =
    Lattice.boundedLatticeOperator
      (((Complex.I * q) / ℏ) •
        AlgebraicFock.dGamma (LatticeState Site) (K.bondOperator x y))
  rw [AlgebraicFock.dGamma_smul]

/-- The historical bounded bond-current/current-current retarded kernel supplied to the general Kubo
API. It is definitionally a specialization of the generic measured-current/source adapter.

This remains deliberately not named conductivity: a vector-potential response must also account for
explicit source dependence of the measured current, as developed downstream in issue #444. -/
noncomputable def boundedBondCurrentRetardedSusceptibility
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (ℏ q : ℂ) (K : LocallyFiniteHopping Site)
    (x y u v : Site) (t s : ℝ) : ℂ :=
  boundedMeasuredCurrentRetardedSusceptibility system expectation
    (boundedBondCurrent ℏ q K x y)
    (boundedBondCurrent ℏ q K u v) t s

/-- The generalized one-body-current response recovers the existing electric bond-current response
when supplied with the scaled one-particle bond operator and a bond-current source. -/
theorem boundedOneBodyCurrentRetardedSusceptibility_scaledBondOperator
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (ℏ q : ℂ) (K : LocallyFiniteHopping Site)
    (x y u v : Site) (t s : ℝ) :
    boundedOneBodyCurrentRetardedSusceptibility system expectation
        (((Complex.I * q) / ℏ) • K.bondOperator x y)
        (boundedBondCurrent ℏ q K u v) t s =
      boundedBondCurrentRetardedSusceptibility system expectation
        ℏ q K x y u v t s := by
  rw [boundedOneBodyCurrentRetardedSusceptibility,
    boundedBondCurrentRetardedSusceptibility,
    boundedOneBodyCurrent_scaledBondOperator]

end
end Transport
end Fermionic
end SecondQuantization
