import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.Bounded
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.GeneralizedQuantity.ConventionalCurrent
import LeanCondensedMatter.QuantumTheory.LinearResponse.RetardedSusceptibility

set_option linter.style.header false

/-!
# Bounded generalized-current response adapters

This module is intentionally downstream of both `Fermionic.Field` and `Fermionic.Lattice`.
The field layer owns the representation-independent generalized-current construction, while the
lattice layer owns the finite-dimensional bounded realization.  Here those two paths meet the
observable-generic Kubo API.

A one-particle current operator `j` is transported by

```text
j  ↦  dΓ(j)  ↦  boundedLatticeOperator (dΓ(j)).
```

The measured current and the source-coupling observable remain separate inputs to the response.
Thus the primitive bounded adapter is `χᴿ_{J,B}`, not a hard-coded current-current correlator.
The older bond-current/current-current wrapper is retained as a charge specialization, and the
one-particle bond operator recovers it by theorem.

This module still does not call a retarded susceptibility a conductivity.  If the measured observable
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
  rw [boundedOneBodyCurrent, AlgebraicFock.dGamma_smul,
    Lattice.boundedLatticeOperator_smul]

/-- Bounded realization of the conventional generalized current `jᵐ = 1/2 {v,m}`.

This is a convenience constructor for the internal/local cases where the generalized balance-law
layer has proved that the conventional current is an admissible current representation. -/
noncomputable def boundedConventionalCurrent
    (velocity m : LatticeState Site →ₗ[ℂ] LatticeState Site) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  boundedOneBodyCurrent
    (Field.conventionalCurrent (LatticeState Site) velocity m)

@[simp]
theorem boundedConventionalCurrent_smul_id
    (velocity : LatticeState Site →ₗ[ℂ] LatticeState Site) (q : ℂ) :
    boundedConventionalCurrent velocity (q • LinearMap.id) =
      q • boundedOneBodyCurrent velocity := by
  rw [boundedConventionalCurrent,
    Field.conventionalCurrent_smul_id,
    boundedOneBodyCurrent_smul]

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
transport.  No choice of charge, spin, or orbital current convention is imposed here. -/
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

/-- Kubo response of the conventional current `1/2 {v,m}` when that current representation has
been justified by the upstream generalized-balance-law hypotheses. -/
noncomputable def boundedConventionalCurrentRetardedSusceptibility
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (velocity m : LatticeState Site →ₗ[ℂ] LatticeState Site)
    (source : FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (t s : ℝ) : ℂ :=
  boundedMeasuredCurrentRetardedSusceptibility system expectation
    (boundedConventionalCurrent velocity m) source t s

/-- The charge-like internal quantity `m = q I` reduces the bounded conventional current to `qv`. -/
theorem boundedConventionalCurrentRetardedSusceptibility_smul_id
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (velocity : LatticeState Site →ₗ[ℂ] LatticeState Site) (q : ℂ)
    (source : FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (t s : ℝ) :
    boundedConventionalCurrentRetardedSusceptibility system expectation
        velocity (q • LinearMap.id) source t s =
      boundedMeasuredCurrentRetardedSusceptibility system expectation
        (q • boundedOneBodyCurrent velocity) source t s := by
  rw [boundedConventionalCurrentRetardedSusceptibility,
    boundedConventionalCurrent_smul_id]

/-- The one-particle operator underlying the existing oriented electric bond current is exactly a
special case of `boundedOneBodyCurrent`. -/
theorem boundedOneBodyCurrent_scaledBondOperator
    (ℏ q : ℂ) (K : LocallyFiniteHopping Site) (x y : Site) :
    boundedOneBodyCurrent (((Complex.I * q) / ℏ) • K.bondOperator x y) =
      boundedBondCurrent ℏ q K x y := by
  rw [boundedOneBodyCurrent, AlgebraicFock.dGamma_smul,
    Lattice.boundedLatticeOperator_smul]
  rfl

/-- The historical bounded bond-current/current-current retarded kernel supplied to the general Kubo
API.  It is now definitionally a specialization of the generic measured-current/source adapter.

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
