# Architecture checks

Architecture CI has two deliberately different layers:

```text
Python pre-build audit
  repository files / direct imports / declarative DAGs / reachability / source contracts
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

CI runs the full registered Python audit once. The runner loads checker `main()` functions into one
Python process instead of spawning one process per checker.

The optional local scopes are organizational filters only:

- `core`: repository-wide, transport, current, and graph topology checks;
- `second-quantization`: SecondQuantization-specific layout/topology checks;
- a checker registered with scope `all` participates in both focused scopes.

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

- required files and directories;
- direct Lean import edges;
- exact umbrella/import exposure when the source edge itself is the contract;
- dependency direction between source trees;
- repository and scoped layer DAGs;
- transitive source reachability when it is itself an architecture boundary;
- narrow source-syntax contracts when syntax itself is intentionally the invariant.

Python may inspect Lean source syntax only when **syntax itself** is intentionally the invariant. The
main example is a compatibility-forwarding file that may be absent from the compiled public
environment. Forwarding files are checked with an allowlist of permitted source commands rather than
a regex attempting to enumerate Lean declarations.

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
ranges, and accumulates violations before failing. Private declarations are normalized to their
user-facing names before namespace/name contracts are applied.

Do not add a Python declaration regex or helper-name scan when the compiled environment can express
the rule. Proof bodies and implementation helper choices are **not architecture contracts**.

## Declarative source graphs

`check_architecture_graphs.py` is the single Python owner of dependency graph structure. Durable DAGs
and transitive reachability contracts are data under `scripts/architecture/`, not checker-local rank
tables, blacklists, or DFS implementations.

The graph data is split by purpose:

- `second_quantization.json`: repository/SecondQuantization layer graph plus scoped
  SecondQuantization DAGs;
- `source_topology.json`: focused Transport, current, LinearResponse, density/Gibbs/entropy, and
  transitive reachability graphs;
- `ahe_topology.json`: canonical Massive-Dirac Model/Intrinsic and completed Bastin stage DAGs.

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

Canonical finite-disorder closure layers
  Core.FiniteTrace → {Streda.TraceKernel, Disorder.Finite}
  Disorder.Finite → {Disorder.Moments, Disorder.Resolvent, Disorder.SCBA}
  Resolvent.Basic → {Disorder.Resolvent, Disorder.SCBA}
  {Disorder.Moments, Disorder.Resolvent} → {Disorder.Born, Disorder.AdvancedBorn}

LinearResponse
  FreeDynamics → PureStateDynamics → PictureEquivalence → {ConservationLaws, EquationsOfMotion}
  Expectation → {DensityExpectation, Stationarity}
  FreeDynamics → Stationarity → ConservationLaws
  DensityExpectation → ConservationLaws

Massive-Dirac AHE foundation
  Model.Basic → Model.Operator
  Model.Basic → Model.Kinematics → Model.Occupation
  Model.Basic → Model.Spectral
  {Model.Operator, Model.Spectral} → Model.OperatorSpectral
  Model.Spectral → Intrinsic.BerryBridge → Intrinsic.BerrySymmetry
                 → Intrinsic.Response → Intrinsic.Conductivity

Massive-Dirac Bastin stages
  Intrinsic geometry → Foundation → Pole → Pair → Radial → Zero-T
                                    ↑
                     Intrinsic conductivity
```

The Bastin stage graph is intentionally coarser than the exact direct-import chain. The #1606–#1612
canonicalization is protected separately by direct-import regression guards, while the DAG records
the durable allowed direction between mathematical stages.

The graph runner also owns the Combinatorics low-level forbidden-transitive-reachability contract.
Every scoped graph is checked with a fresh diagnostic buffer so a failure in one graph cannot suppress
validation or import diagnostics from later graphs.

Python uses longest-prefix classification for source DAGs. The primary graph is also consumed by the
Lean audit, whose lookup is order-based, so the Python pre-build audit requires primary module
prefixes from different layers to be non-overlapping. That partition invariant guarantees both
consumers classify the shared primary graph identically.

## Declarative positive source contracts

A required direct import is deliberately not encoded merely as an allowed DAG edge: a DAG says which
direction is legal, not that one exact edge must exist.

`source_contracts.json` therefore owns the uniform positive topology that used to be spread over many
small focused Python scripts. `check_source_contracts.py` currently checks:

- required canonical files;
- required canonical directories;
- required direct imports.

This includes the thin QuantumTheory, SingleParticle, SecondQuantization AlgebraicFock/Lattice/mode,
density/Gibbs, transport/validation owner, and Bloch–de Dominicis topology contracts. Their semantic
owner/type rules remain in the compiled Lean audit.

Special topology stays in a focused Python checker only when it is not yet a uniform data contract,
for example layered directory layout or compatibility-forwarding/regression contracts.

## Compatibility forwarding files

Transport and AHE compatibility modules are temporary source-topology objects. Their defining source
contract is deliberately narrow: after comments are stripped, only

- `import ...` commands,
- blank lines, and
- `set_option linter.style.header false`

are accepted. This is stronger and more future-proof than maintaining a declaration regex that can
miss `private`, `opaque`, `axiom`, `instance`, or future Lean declaration forms.

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

`architecture_graph_scopes.py` owns scoped-DAG loading and transitive-reachability execution.
`check_source_contracts.py` owns uniform positive file/directory/direct-import contracts.

The old `ImportBoundary`, checker-local dependency traversal, declaration-scanning helpers, and generic
semantic source-matching helpers have been removed. Focused checkers should not implement a second
Lean parser or dependency traversal.

## One owner per architectural concern

A durable layer graph has one authoritative specification and one graph runner. A uniform positive
source contract has one data specification and one runner. A declaration-level invariant has one
compiled Lean contract. Once an invariant is migrated, delete its superseded parser, blacklist, DFS,
token scan, or one-off data-only checker instead of retaining duplicate guards.

```text
allowed dependency direction → declarative DAG data
required source topology      → source_contracts.json / focused syntax-layout checks
compiled meaning              → Lean
```

## Adding source topology

1. Ask whether the rule is a dependency direction/reachability rule or a required concrete edge.
2. Put direction/reachability into an architecture graph under `scripts/architecture/`.
3. Put uniform required files/directories/direct imports into `source_contracts.json`.
4. Add a focused Python checker only for a genuinely distinct layout/syntax/migration contract.
5. Reuse shared primitives and register each checker once in `check_architecture.py`.

## Adding a compiled semantic check

1. Express the invariant as a pure `Snapshot → Array String` check in `CheckArchitecture.lean` where
   possible.
2. Reuse declaration/module/type helpers rather than reparsing source text.
3. Register the check in the single compiled-check array.
4. Delete any Python declaration or helper-body parser made redundant by the new contract.
5. Keep mathematical identities in ordinary Lean theorems; architecture CI should verify stable
   contracts, not a preferred proof route.
