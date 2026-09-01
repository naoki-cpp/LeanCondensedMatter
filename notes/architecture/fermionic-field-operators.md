# Fermionic field-operator architecture

## Representations

The basis-independent algebraic fermionic Fock space is

```text
SecondQuantization.Fermionic.AlgebraicFock 𝓗₁ = ExteriorAlgebra ℂ 𝓗₁.
```

Creation is exterior multiplication and annihilation is contraction by the corresponding dual
functional. A chosen ordered mode basis gives the occupation representation
`Fermionic.OccupationFock Mode`, with an explicit linear equivalence to `AlgebraicFock` that
intertwines the ladder operators.

The completed representation

```text
SecondQuantization.Fermionic.CompletedFockSpace Mode
```

is a distinct `ℓ²` occupation Hilbert space. Algebraic and occupation-space identities do not by
themselves imply boundedness or domain properties on that completion.

## One-body conservation/current ownership

Particle-statistics-independent one-body balance and current semantics stay upstream:

```text
Analysis.Operator.LinearCommutator
        ↓
Analysis.Calculus.OneBodyBalance
        ↓
Analysis.Calculus.CurrentRepresentation
        ↓
QuantumTheory.ConservationLaw
```

`Analysis` owns representation-independent commutator/balance/current interfaces.
`QuantumTheory.ConservationLaw` owns the quantum specialization, including Heisenberg transport and
the conventional current `1/2 {v,m}`.

Fermionic second quantization consumes those definitions and owns only representation-specific lifts,
such as preservation under `dGamma`.

## Fermionic ownership

```text
Fermionic.Algebra
      ↓
Fermionic.Lattice
      ↓
Fermionic.Transport
      ↓
Fermionic.Validation
```

`Fermionic.Lattice` owns discrete one-particle lattice data, hopping, charge/bond currents, Peierls
families, finite-lattice bounded realizations, and model-level current identities. It does not own
generic response, conductivity, disorder, or validation theory.

`Fermionic.Field` is a narrow side interface for basis-independent density constructions, continuum
density specializations, and the `dGamma` bridge for generalized localized quantities. It does not
own generic one-body current semantics or lattice/transport models.

`Fermionic.Transport` is the downstream specialization layer for fermionic response. It consumes
bounded lattice currents together with generic `QuantumTheory` linear response and the generic
`LeanCondensedMatter.Transport` resolvent/disorder/transport infrastructure. Fermionic modules should
not duplicate generic resolvent, disorder, trace, or Středa APIs.

The generalized-current specialization remains layered as

```text
bounded one-body current → dGamma current response
                        ↓
              conventional current
                        ↓
              spin/concrete currents.
```

`Fermionic.Validation` is terminal: it may consume public algebra, lattice, and transport APIs, but
foundational layers must not depend on it.

## Bounded response boundary

The exterior-algebra construction supports algebraic identities without completion. Bounded
finite-lattice response uses the finite-dimensional Hilbert realization only after the relevant
operators have been transported and bounded. Completed-space operators and unbounded domains remain
owned by `Fermionic.CompletedSpace`, not by the transport layer.
