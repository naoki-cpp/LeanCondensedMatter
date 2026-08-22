# Architecture checks

Architecture CI has two deliberately different layers:

```text
Python pre-build audit
  repository files / direct imports / declarative DAGs / reachability
        ↓
lake build --wfail + lint
        ↓
Lean post-build audit
  compiled declarations / owners / namespaces / declaration types / semantic contracts
        ↓
compiled sorryAx audit
```

`check_architecture.py` is the single CI entry point for Python architecture checks.
`scripts/CheckArchitecture.lean` is the single post-build entry point for compiled semantic
architecture checks.

## Python execution

CI runs the full registered Python audit once. Individual checker scripts remain directly executable
for local debugging, but the runner loads their `main()` functions into one Python process instead of
spawning one process per checker.

The optional local scopes are only organizational filters:

- `core`: repository-wide, QuantumTheory, transport, single-particle, and graph topology checks;
- `second-quantization`: SecondQuantization file/import/layout checks.

Run the same Python audit as CI with:

```bash
python3 scripts/check_architecture.py
```

Run a focused local subset with:

```bash
python3 scripts/check_architecture.py --scope core
python3 scripts/check_architecture.py --scope second-quantization
```

After the library has been built, run the compiled audit with:

```bash
lake env lean scripts/CheckArchitecture.lean
```

## Responsibility boundary

Architecture CI describes the repository's **current architecture**, not the sequence of refactors
that produced it. The authoritative mechanism must match the kind of invariant.

### Python owns source topology

Keep these checks in the lightweight pre-build audit:

- required files and umbrella layout;
- direct Lean import edges;
- dependency direction between source trees;
- repository and scoped layer DAGs;
- transitive source reachability when it is itself an architecture boundary;
- exact umbrella/import exposure when the source edge itself is the contract.

Python may inspect Lean source syntax only when **syntax itself** is intentionally the invariant. The
main remaining example is a compatibility-forwarding file that must contain imports but own no Lean
declarations. Such a file may not be imported by the public library at all, so the compiled
environment is intentionally not the authority for that forwarding-only property.

Comment stripping in `architecture_audit_common.py` exists to make direct-import and the small number
of deliberate syntax checks comment-aware. It is not a general semantic Lean parser.

### Lean owns compiled semantics

Use `CheckArchitecture.lean` for invariants that are naturally properties of the elaborated
environment:

- canonical declaration ownership;
- declaration-name/module ownership relationships;
- declaration namespace/module relationships;
- declaration type/signature dependencies;
- dimension-independence expressed by compiled signatures;
- semantic bridge contracts expressed by typed declarations or theorems.

The compiled harness collects `LeanCondensedMatter` declarations once, resolves declaration-to-module
ownership through `Environment.const2ModIdx`, records whether declarations correspond to source
ranges, and accumulates all violations before failing. Private declarations are normalized to their
user-facing names before namespace/name contracts are applied.

Do not add a Python declaration regex or helper-name scan when the compiled environment can express
the rule. In particular, proof bodies and implementation helper choices are **not architecture
contracts**. A theorem may be reproved or a definition refactored without changing CI as long as its
stable owner, namespace, type, and mathematical API contract remain valid.

## Declarative source graphs

`check_architecture_graphs.py` is the **single Python owner of dependency graph structure**. Durable
DAGs and transitive reachability contracts are data under `scripts/architecture/`, not checker-local
rank tables, blacklists, or DFS implementations.

The graph data is split by purpose:

- `second_quantization.json`: repository/SecondQuantization layer graph plus scoped
  SecondQuantization DAGs;
- `source_topology.json`: focused Transport, current, LinearResponse, density/Gibbs/entropy, and
  transitive reachability graphs.

For a direct import from source layer `A` to target layer `B`, the rule is:

```text
A = B
or
B is an ancestor of A
```

Edges are written upstream → downstream. Downstream and sibling imports are therefore rejected by
reachability rather than repeated forbidden-import lists.

Representative centralized graphs include:

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

The graph runner also owns the Combinatorics low-level forbidden-transitive-reachability contract.

A required direct import is deliberately not encoded merely as an allowed DAG edge: a DAG says which
direction is legal, not that one exact edge must exist. Focused topology checkers may therefore retain
required imports and exact umbrella exposure without duplicating the architecture DAG.

See `scripts/architecture/README.md` for the graph schema.

## Compiled semantic contracts

The Lean audit currently protects, among other things:

- canonical QuantumTheory state/dynamics/POVM/density owners;
- path-owned SecondQuantization and SingleParticle namespaces;
- bounded-response and mode-foundation dimension independence at declaration-type level;
- separation of normalized expectation from dynamics implementation layers;
- diagonal density formulas from entropy implementation layers;
- typed physical-real-scalar bridges rather than `.re`/helper text snapshots;
- pure-point/Gibbs/entropy and Bloch–de Dominicis semantic endpoints.

When a semantic boundary needs strengthening, add a typed theorem or declaration relationship and
audit that compiled contract. Do not freeze the proof tactic, body helper, or source spelling that
happens to establish it today.

## Shared Python audit primitives

`architecture_audit_common.py` provides repository-wide source-topology mechanics:

- deterministic file discovery;
- comment-aware direct-import parsing;
- module-prefix matching;
- file/import requirements;
- graph loading, classification, reachability, and DAG validation.

The old `ImportBoundary`, `check_import_boundaries`, `forbid_import_prefixes`, declaration-scanning
helpers, and generic source-matching helpers have been removed as their responsibilities moved to the
shared graph audit or compiled Lean audit.

Because the full Python audit runs in one read-only process, source/import views are cached. Focused
checkers should not implement a second Lean parser or dependency traversal.

## One owner per architectural concern

A durable layer graph has one authoritative specification and one graph runner. A declaration-level
invariant has one compiled Lean contract. Once an invariant is migrated, delete its superseded
parser, blacklist, DFS, or token scan instead of retaining duplicate guards.

The same rule applies across languages:

```text
source topology  → Python
compiled meaning → Lean
```

## Adding source topology

1. Ask whether the rule is an edge/subgraph or reachability contract of an existing declarative graph.
2. If yes, edit a specification under `scripts/architecture/`; do not add checker-local traversal.
3. Add a focused Python check only for a distinct file/import/syntax contract.
4. Reuse shared primitives and register the checker once in `check_architecture.py`.

## Adding a compiled semantic check

1. Express the invariant as a pure `Snapshot → Array String` check in `CheckArchitecture.lean` where
   possible.
2. Reuse declaration/module/type helpers rather than reparsing source text.
3. Register the check in the single compiled-check array.
4. Delete any Python declaration or helper-body parser made redundant by the new contract.
5. Keep mathematical identities in ordinary Lean theorems; architecture CI should verify stable
   contracts, not a preferred proof route.
