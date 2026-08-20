# Fermionic field-operator architecture

## Algebraic Fock space

The basis-independent algebraic fermionic Fock space is

```text
SecondQuantization.Fermionic.AlgebraicFock 𝓗₁
  = ExteriorAlgebra ℂ 𝓗₁.
```

It is algebraic rather than a completed Hilbert direct sum. No finite-dimensionality assumption is
required, and general second-quantized operators are not assumed bounded.

## Field operators

Creation by `f : 𝓗₁` is left exterior multiplication by the degree-one image of `f`.
Annihilation by a dual vector is left contraction. On an inner-product space, the physical
annihilation operator uses the dual `g ↦ inner ℂ f g` and is conjugate-linear in `f`.

An orthonormal family defines mode operators by smearing these fields. Their CAR follow from the
exterior multiplication and contraction identities.

## Occupation representation

`SecondQuantization.Fermionic.OccupationFock Mode` is the free complex vector space on finite
occupation subsets of an ordered mode type. Its name records that this is the representation built
from a chosen mode basis, rather than the basis-independent exterior-algebra construction.

A linearly ordered basis `b : Module.Basis Mode ℂ 𝓗₁` induces the explicit linear equivalence

```text
AlgebraicFock.occupationEquiv b :
  Fermionic.OccupationFock Mode ≃ₗ[ℂ] Fermionic.AlgebraicFock 𝓗₁.
```

`OccupationFieldEquivalence.lean` proves that this equivalence intertwines occupation creation with
exterior multiplication and occupation annihilation with contraction by the matching coordinate
functional.

## Completed representation

`SecondQuantization.Fermionic.CompletedFockSpace Mode` is a third, distinct representation: the
completed `ℓ²` occupation space. Neither `OccupationFock` nor `AlgebraicFock` denotes that analytic
completion.

## Generic one-body conservation/current owner

Generalized one-body transport is not owned by the fermionic field layer.

The reusable dependency chain is

```text
Analysis.Operator.LinearCommutator
        ↓
Analysis.Calculus.OneBodyBalance
        ↓
Analysis.Calculus.CurrentRepresentation
        ↓
QuantumTheory.ConservationLaw
  CurrentRepresentation
  HeisenbergTransport
  ConventionalCurrent
  concrete Schwartz realizations
```

`Analysis` owns the representation-independent linear-map commutator, symmetric localization,
transport/source balance decomposition, and weak current-representation interfaces.
`QuantumTheory.ConservationLaw` owns the particle-statistics-independent quantum specialization:
Heisenberg scaling, the conventional current `1/2 {v,m}`, and concrete first-quantized current
realizations.

Fermionic second quantization consumes the canonical `ConservationLaw.linearCommutator` directly.
It owns only representation-specific results such as preservation by `dGamma`; no duplicate
`AlgebraicFock` commutator operation or compatibility theorem is part of the public API.

## Lattice model owner

`SecondQuantization.Fermionic.Lattice` is the canonical layer for model data built on the algebraic
fermionic core. It owns discrete one-particle lattice states, locally finite hopping, site charge and
bond currents, Peierls families, finite-lattice bounded realizations, Hermiticity/current identities,
rank-one lattice specializations, and geometric current aggregation.

The lattice owner does not import generic Kubo, frequency-response, conductivity, Středa, disorder,
or validation layers. Mixed files are split so model constructions remain under `Lattice` while
response theorems stay downstream. Downstream consumers explicitly qualify or open the `Lattice`
namespace rather than relying on former `Field` ownership.

## Narrow field-interface owner

`SecondQuantization.Fermionic.Field` is intentionally small. It retains basis-independent density
interfaces, continuum density specializations, and the fermionic `dGamma` bridge for generalized
localized quantities. It does **not** own one-body current representations, conventional-current
semantics, concrete Schwartz current models, lattice models, transport response, conductivity, or
validation.

The generalized many-body bridge is therefore

```text
QuantumTheory / Analysis one-body balance
        ↓
Fermionic.Field.GeneralizedQuantity
  dGamma(localized quantity)
  dGamma transport/source identities
```

rather than a current hierarchy rooted under `Field`.

## Transport owner

`SecondQuantization.Fermionic.Transport` is the canonical downstream owner for fermionic response and
transport specializations. It consumes bounded lattice currents and generic `QuantumTheory` response
infrastructure and owns the finite-frequency response chain, conductivity normalization,
Kubo–Greenwood/Bastin adapters, fermionic Středa/Ward bridges, and finite-disorder specialization.
Generic occupation, resolvent, trace, and Středa integration mathematics remains upstream under
`QuantumTheory` and is not duplicated here.

The generalized-current response boundary is split deliberately:

```text
BoundedCurrentResponse
  arbitrary one-body j → dGamma(j) → bounded observable → χᴿ_{J,B}
        ↓
ConventionalCurrentResponse
  j = 1/2 {v,m} specialization
        ↓
SpinCurrentResponse and later concrete current responses
```

Thus the generic bounded response adapter does not depend on the conventional-current formula.

## Validation owner

`SecondQuantization.Fermionic.Validation` contains finite toy models and explicit value/symmetry
checks. It is a terminal consumer of the public algebra, lattice, and transport layers; foundational
or reusable construction layers must not import it.

The stable responsibility direction for fermionic second-quantized code is

```text
Fermionic.Algebra
      ↓
Fermionic.Lattice
      ↓
Fermionic.Transport
      ↓
Fermionic.Validation
```

`Fermionic.Field` is a narrow side interface. Particle-statistics-independent one-body current
semantics enter from `Analysis` / `QuantumTheory.ConservationLaw`, not through `Field`.

## Bounded response boundary

The exterior Fock construction supports algebraic second quantization and current identities without
completion. Bounded finite-lattice operators are introduced in `Fermionic.Lattice.Bounded` after
restricting to a finite site type and transporting the occupation representation to the
finite-dimensional Hilbert Fock realization. Fermionic transport specializations consume those
bounded lattice operators while generic Kubo and transport mathematics remains in `QuantumTheory`.
