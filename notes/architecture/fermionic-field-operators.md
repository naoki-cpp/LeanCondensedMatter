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
Field.occupationEquiv b :
  Fermionic.OccupationFock Mode ≃ₗ[ℂ] Fermionic.AlgebraicFock 𝓗₁.
```

`OccupationFieldEquivalence.lean` proves that this equivalence intertwines occupation creation with
exterior multiplication and occupation annihilation with contraction by the matching coordinate
functional.

## Completed representation

`SecondQuantization.Fermionic.CompletedFockSpace Mode` is a third, distinct representation: the
completed `ℓ²` occupation space. Neither `OccupationFock` nor `AlgebraicFock` denotes that analytic
completion.

## Bounded response boundary

The exterior Fock construction supports algebraic second quantization and current identities without
completion. Bounded operators used by the Kubo layer are introduced only after restricting to a
finite site type and transporting the occupation representation to the finite-dimensional Hilbert
Fock realization.
