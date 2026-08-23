# Declarative architecture data

Files in this directory are architecture **specifications**, not checker implementations.

The goal is to describe durable repository topology as data, then let the architecture audits
interpret it at the appropriate level.

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

Python classifies graph modules by longest matching prefix. The compiled Lean namespace audit reads
the same primary graph with first-match lookup, so the pre-build audit additionally requires primary
module prefixes owned by different layers to be non-overlapping. That partition invariant makes the
two classification rules equivalent. Scoped source-only DAGs may still use nested prefixes because
they are interpreted only by Python's longest-prefix classifier.

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

`source_topology.json` contains repository source-layer DAGs that do not belong to the compiled
SecondQuantization namespace contract. The finite-disorder graph is expressed in terms of the
**canonical** Transport modules rather than compatibility forwarders:

```text
Transport.Core.FiniteTrace
  ├→ Transport.Streda.TraceKernel
  └→ Transport.Disorder.Finite

Transport.Disorder.Finite
  ├→ Transport.Disorder.Moments
  ├→ Transport.Disorder.Resolvent
  └→ Transport.Disorder.SCBA

Transport.Resolvent.Basic
  ├→ Transport.Disorder.Resolvent
  └→ Transport.Disorder.SCBA

{Transport.Disorder.Moments, Transport.Disorder.Resolvent}
  ├→ Transport.Disorder.Born
  └→ Transport.Disorder.AdvancedBorn
```

It also contains the LinearResponse, generalized-current, density/Gibbs/entropy, and other focused
source DAGs.

`ahe_topology.json` starts the stable canonical Massive-Dirac AHE graph without freezing the Bastin
migration while it is still evolving:

```text
Model.Basic ─┬→ Model.CurrentBridge
             └→ Model.Spectral → Intrinsic.BerryBridge
                                → Intrinsic.BerrySymmetry
                                → Intrinsic.Response
                                → Intrinsic.Conductivity
```

## Positive source contracts

A dependency-direction DAG answers **which layers may depend on which upstream layers**. It does not
assert that a particular direct edge must exist.

Fixed positive topology therefore lives separately in `source_contracts.json`. The shared source
contract runner currently supports:

- required canonical files;
- required canonical directories;
- required direct imports.

This replaces checker-local Python files whose only remaining content was a static list of paths and
required edges. A required direct import is deliberately not encoded as an ordinary DAG edge: an
allowed direction and a required edge are different contracts.

Special topology that is not yet a uniform data shape may remain in a focused checker. Examples are
exact umbrella boundaries, layered directory-layout rules, and active compatibility migrations.

## Source syntax contracts

Declaration ownership, namespace ownership, dimension independence, and other semantic signature
constraints belong to the compiled Lean audit, not source-text parsing.

Python inspects syntax only when syntax itself is the invariant. The main example is a compatibility
forwarding module. Such a file may be absent from the compiled public environment, so its forwarding
property is checked directly: after comments are removed, only `import` commands, blank lines, and
the standard `set_option linter.style.header false` command are accepted. This allowlist avoids
trying to maintain a regex enumerating every form of Lean declaration.

## Independent diagnostics

Every primary/scoped DAG is validated and checked with its own fresh diagnostic buffer. A malformed
or violated graph must not prevent later graphs from being validated in the same CI run. Diagnostics
are then accumulated by the top-level architecture audit.

## One graph runner, two semantic levels

`check_architecture_graphs.py` is the single Python owner for the primary graph and all scoped import
DAGs. Individual Python checkers must not restate those dependency-direction edges.

Python owns direct source topology: it classifies source and imported modules through
`modulePrefixes` and checks imports against graph ancestry before the Lean build.

Lean owns compiled semantics. `CheckArchitecture.lean` reads the primary graph from
`second_quantization.json` after the build, resolves each source-declared constant to its compiled
owner module, converts private names back with `privateToUserName`, and checks the layer's
`namespacePrefixes` and `forbiddenNameFragments`. Additional compiled checks protect canonical
owners and declaration-type dependencies that are not naturally represented by the layer DAG.

Scoped DAGs and `source_contracts.json` are source-topology data only; declaration-level rules should
be represented as compiled Lean contracts rather than reintroducing source parsers.

This deliberately avoids teaching Python how to parse Lean `namespace`, `section`, `end`, declaration
modifiers, private-name syntax, proof bodies, or helper-name usage.

## Exceptions

`namespaceExceptions` are for small, intentional semantic crossings that cannot be represented by a
layer namespace alone. They are matched by compiled owner-module prefix plus user-facing declaration
prefix.

Keep this list small. An exception should describe a real architectural choice, not preserve an old
source location after a refactor.

The current SecondQuantization graph has one such exception: the combinatorial
`Combinatorics.Pairing.weight` declaration is implemented in the Common thermal tree while remaining
owned by the `Combinatorics` namespace.
