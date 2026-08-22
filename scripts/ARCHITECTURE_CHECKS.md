# Architecture checks

Architecture CI has two deliberately different layers:

```text
Python pre-build audit
  repository files / direct imports / declarative DAGs / reachability
        ↓
lake build --wfail + lint
        ↓
Lean post-build audit
  compiled declarations / owners / namespaces / public types / semantic contracts
        ↓
compiled sorryAx audit
```

`check_architecture.py` is the single CI entry point for the repository's Python architecture checks.
`scripts/CheckArchitecture.lean` is the single post-build entry point for compiled semantic architecture checks.

## Python execution

CI runs the full registered Python audit once. Individual checker scripts remain focused and directly executable for
local debugging, but the runner loads their `main()` functions into one Python process instead of spawning one process
per checker.

Every registered checker participates in the full CI audit. The runner also exposes two optional local filters:

- `core`: repository-wide, QuantumTheory, transport, single-particle, and graph checks;
- `second-quantization`: SecondQuantization-specific ownership and source-policy checks.

Scopes are organizational filters only. They do not define CI partitions and they do not define or override the
Lean module dependency graph.

Run the same full Python audit as CI with:

```bash
python3 scripts/check_architecture.py
```

Run focused local subsets with:

```bash
python3 scripts/check_architecture.py --scope core
python3 scripts/check_architecture.py --scope second-quantization
```

After the library has been built, run the compiled audit with:

```bash
lake env lean scripts/CheckArchitecture.lean
```

## Responsibility boundary

Architecture CI encodes the repository's **current structure**, not the sequence of refactors that produced it.
The authoritative mechanism should match the kind of invariant.

### Python owns source topology

Keep these checks in the lightweight pre-build Python audit:

- file and umbrella layout;
- direct Lean import edges;
- dependency direction between source trees;
- repository and scoped layer DAGs;
- transitive source reachability when it is itself an architectural boundary;
- source-syntax policy only when syntax itself is intentionally the contract.

### Lean owns compiled semantics

Prefer `CheckArchitecture.lean` for invariants that are naturally properties of the compiled environment:

- canonical declaration ownership;
- declaration-name/module ownership relationships;
- declaration namespace/module relationships;
- public type/signature dependencies;
- semantic contracts expressible by typed Lean declarations or theorems.

The compiled harness collects all `LeanCondensedMatter` declarations once, resolves declaration-to-module ownership
through `Environment.const2ModIdx`, marks whether each declaration has a source declaration range, and accumulates all
violations before failing. Private declarations are normalized to their user-facing names before namespace/name
contracts are applied.

Do not add a Python regex owner scan when the compiled environment can express the same rule directly.

## Declarative architecture graphs

`check_architecture_graphs.py` is the **single Python owner of dependency graph structure**. Durable DAGs and transitive
reachability contracts are data under `scripts/architecture/`, not checker-local boundary tables, layer ranks,
forbidden-import loops, or custom DFS implementations.

The graph data is split by purpose:

- `second_quantization.json`: the primary repository/SecondQuantization layer graph plus scoped SecondQuantization DAGs;
- `source_topology.json`: focused Transport, current, LinearResponse, density/Gibbs/entropy, and transitive reachability graphs.

For a direct import from source layer `A` to target layer `B`, the rule is:

```text
A = B
or
B is an ancestor of A
```

Edges are written upstream -> downstream, so downstream and sibling imports are rejected by reachability rather than
by repeated blacklists.

The centralized graphs include:

```text
math → quantumTheory → common → {fermionic, bosonic}

Algebra → {Field, Lattice} → Transport → Validation

Semantics → Factorization → Analysis → Integration → Series

CompletedSpace → Thermal

Analysis current algebra
  LinearCommutator → SymmetrizedProduct
  CurrentRepresentation → BalanceLaw
  {BalanceLaw, SymmetrizedProduct} → SymmetricLocalization

Single-particle current
  LocalizedTransport → SymmetrizedVelocityCurrent
  SymmetrizedVelocityCurrent → {ConventionalCurrent, SchwartzCurrent, SchwartzSpinCurrent}

Generic Transport → SecondQuantization

Finite-disorder closure layers
  FiniteTrace → {StredaTraceKernel, FiniteDisorder}
  FiniteDisorder → {Moments, DisorderResolvent, SCBA}
  Resolvent → {DisorderResolvent, SCBA}
  {Moments, DisorderResolvent} → {Born, AdvancedBorn}

LinearResponse
  FreeDynamics → PureStateDynamics → PictureEquivalence → {ConservationLaws, EquationsOfMotion}
  Expectation → {DensityExpectation, Stationarity}
  FreeDynamics → Stationarity → ConservationLaws
  DensityExpectation → ConservationLaws

Density / Gibbs / entropy
  DiagonalFormula → PurePoint / diagonal consumers
  {PurePoint, FiniteHilbertOperator} → FiniteGibbsExpectationBridge
  {Entropy, PurePoint} → FreeEntropy
```

The graph runner also owns the Combinatorics low-level **forbidden transitive reachability** contract, replacing the old
standalone DFS checker.

Focused Python scripts must not restate these graph edges. They may retain genuinely different contracts such as:

- required direct imports (`A must import B`);
- exact umbrella exposure;
- required source files/layout;
- finite-dimensionality restrictions or other genuine source semantic policy.

A required import is deliberately not encoded as a DAG edge: a DAG says which direction is legal, not that the edge
must exist. Keeping those concepts separate avoids turning the architecture graph into an exact source snapshot.

See `scripts/architecture/README.md` for the graph schema and current graphs.

## Shared Python audit primitives

Use `architecture_audit_common.py` for repository-wide source mechanics instead of checker-local infrastructure. The
common layer provides comment-aware direct imports, module-prefix matching, file requirements, graph loading,
classification, reachability, and DAG validation.

The superseded `ImportBoundary`, `check_import_boundaries`, and `forbid_import_prefixes` helpers have been removed.
Durable dependency direction belongs in the shared graph specifications instead of a second imperative boundary API.

Because the full Python audit runs in one read-only process, common source/import views are cached. Generic import
parsing, module-prefix semantics, source scans, and dependency traversal should not be reimplemented in focused
checkers.

## One owner per architectural concern

A durable layer graph has one authoritative specification and one graph runner. Focused checkers add only constraints
specific to their mathematical domain. Once an invariant is migrated, delete its superseded parser, blacklist, DFS, or
forbidden-import loop rather than keeping duplicate guards.

The same rule applies across languages: declaration-level invariants belong to the compiled Lean audit; source import
DAGs belong to the Python graph audit.

## Prefer durable contracts

Prefer a layer graph over repeated forbidden-downstream lists. Prefer required public umbrellas as a set over pinning
source order unless order itself is part of the contract. For compiled checks, prefer declaration owner, public type,
namespace, or theorem contracts over implementation-body text.

Do not preserve migration history in permanent CI. Retired-file guards should exist only when reintroduction remains a
realistic architectural ambiguity; proof-helper text should not become an architecture contract.

## Adding source topology

1. First ask whether the rule is an edge/subgraph or reachability contract of an existing declarative graph.
2. If yes, edit a specification under `scripts/architecture/`; do not add checker-local traversal.
3. Add a focused `check_*.py` only for a genuinely distinct non-graph source contract.
4. Reuse shared primitives and register the checker once in `check_architecture.py`.

## Adding a compiled semantic checker

1. Express the invariant as a pure `Snapshot → Array String` check in `CheckArchitecture.lean` where possible.
2. Reuse declaration/module/type helpers rather than reparsing source text.
3. Register the check in the single compiled-check array.
4. Remove any Python declaration parser that becomes redundant.
5. Keep mathematical identities in ordinary Lean theorems; architecture CI should verify stable contracts, not a preferred proof route.
