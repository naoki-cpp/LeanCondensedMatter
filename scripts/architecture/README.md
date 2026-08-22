# Declarative architecture graphs

Files in this directory are architecture **specifications**, not checker implementations.

The goal is to describe repository dependency direction by naming graph vertices and edges once,
then let the architecture audits interpret that data at the appropriate level.

## Primary layer graph

Each primary layer declares:

- `id`: stable graph vertex name;
- `modulePrefixes`: Lean modules classified into that vertex;
- `namespacePrefixes`: compiled declaration namespaces allowed for modules in that vertex;
- `forbiddenNameFragments`: semantic declaration-name fragments forbidden in that layer.

Edges are oriented **upstream -> downstream**. A direct source import from layer `A` to layer `B` is
valid exactly when `A = B` or `B` is an ancestor of `A` in the graph. The checker computes graph
reachability, so transitive dependencies do not need to be repeated as extra edges.

For `second_quantization.json`, the primary graph is:

```text
math ───────→ quantumTheory
  └─────────→ common ←──── quantumTheory
                 ├────→ fermionic
                 └────→ bosonic
```

Consequences follow from the graph rather than separate blacklists:

- `Common` cannot import `Fermionic` or `Bosonic`;
- `Analysis` / `Combinatorics` / `QuantumTheory` cannot import SecondQuantization layers downstream;
- `Fermionic` and `Bosonic` cannot import each other;
- both statistics-specific layers may consume `Common` and its upstream ancestors.

## Scoped import DAGs

Some architectures are meaningful only inside a focused source region. Encoding them in the primary
graph would turn unrelated modules into one artificial global ordering, so specifications also
support `scopedImportGraphs`.

Each scoped DAG declares:

- `id`: diagnostic name;
- `sourceRoots`: repository directories whose direct imports are checked;
- `layers`: local graph vertices with `modulePrefixes`;
- `edges`: local upstream -> downstream dependency edges.

Targets outside the scoped graph are intentionally ignored. This lets a focused graph describe only
the dependency relation it owns without duplicating unrelated repository policy.

`second_quantization.json` contains the SecondQuantization-centered DAGs:

```text
Fermionic
  Algebra → {Field, Lattice} → Transport → Validation

TwoPointDiagramExpansion
  Semantics → Factorization → Analysis → Integration → Series

Fermionic
  CompletedSpace → Thermal

Bosonic Quartic
  Semantics → Thermal

QuantumTheory → {SingleParticle, SecondQuantization}

Combinatorics → Permutation
```

It also keeps Fermionic lattice construction upstream of response theory and AlgebraicFock upstream
of transport-specific quantum theory.

`source_topology.json` contains the remaining repository source-layer DAGs that do not belong to the
compiled SecondQuantization namespace contract:

```text
Generic Transport → SecondQuantization

Finite disorder
  FiniteDisorder ─────→ Moments ───────────┐
        │                   └──────────────→│ Born
        ├────────→ DisorderResolvent ─────→│ AdvancedBorn
        │                 ↑                 │
        └─────────────────┼──────────────→ SCBA
                  Resolvent ─────────────→ SCBA

LinearResponse
  FreeDynamics → PureStateDynamics → PictureEquivalence → {ConservationLaws, EquationsOfMotion}
  Expectation → DensityExpectation → ConservationLaws
  Expectation → Stationarity ← FreeDynamics
  Stationarity → ConservationLaws

Density / Gibbs / entropy
  DiagonalFormula → PurePoint → FiniteGibbsExpectationBridge
  FiniteHilbertOperator ────────────────→ FiniteGibbsExpectationBridge
  Entropy → FreeEntropy ← PurePoint
```

A focused generalized-current graph additionally prevents representation-independent Analysis
modules and the fermionic field bridge from depending on concrete `QuantumMechanics`.

## What is not a DAG

A dependency-direction DAG answers **which layers may depend on which upstream layers**. It does not
assert that a particular direct edge must exist.

Therefore contracts such as:

- `A` must directly import `B`;
- an umbrella must export a particular module set;
- a file must exist at a canonical path;

remain focused positive-edge/layout policy. They should not be encoded as fake DAG edges merely to
put every topology check in one data structure.

Likewise, source-level semantic guards such as finite-dimensionality restrictions remain outside the
DAG when syntax or a particular source boundary is itself the intended contract.

## One graph runner, two semantic levels

`check_architecture_graphs.py` is the single Python owner for the primary graph and all scoped import
DAGs. Individual Python checkers must not restate those dependency-direction edges.

Python owns direct source topology: it classifies source and imported modules through
`modulePrefixes` and checks imports against graph ancestry before the Lean build.

Lean owns compiled semantics. `CheckArchitecture.lean` reads the primary graph from
`second_quantization.json` after the build, resolves each source-declared constant to its compiled
owner module, converts private names back with `privateToUserName`, and checks the layer's
`namespacePrefixes` and `forbiddenNameFragments`.

Scoped DAGs are import-topology data only; declaration-level rules should be represented as compiled
Lean contracts rather than reintroducing source parsers.

This deliberately avoids teaching Python how to parse Lean `namespace`, `section`, `end`, declaration
modifiers, or private-name syntax.

## Exceptions

`namespaceExceptions` are for small, intentional semantic crossings that cannot be represented by a
layer namespace alone. They are matched by compiled owner-module prefix plus user-facing declaration
prefix.

Keep this list small. An exception should describe a real architectural choice, not preserve an old
source location after a refactor.

The current SecondQuantization graph has one such exception: the combinatorial
`Combinatorics.Pairing.weight` declaration is implemented in the Common thermal tree while remaining
owned by the `Combinatorics` namespace.
