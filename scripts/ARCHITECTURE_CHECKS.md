# Architecture checks

Architecture CI has two deliberately different layers:

```text
Python pre-build audit
  repository files / direct imports / declarative layer DAGs
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

- `core`: repository-wide, QuantumTheory, transport, single-particle, and combinatorics checks;
- `second-quantization`: SecondQuantization-specific ownership and dependency checks.

Scopes are organizational filters only. They do not define CI partitions and they do not define or override the
Lean module dependency graph. Each checker is registered exactly once, and the runner rejects unregistered
`check_*.py` scripts except for explicitly listed non-architecture utilities.

Run the same full Python audit as CI with:

```bash
python3 scripts/check_architecture.py
```

Run a focused local subset with:

```bash
python3 scripts/check_architecture.py --scope core
python3 scripts/check_architecture.py --scope second-quantization
```

List registered checks without executing them with:

```bash
python3 scripts/check_architecture.py --list
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
violations before failing. Generated declarations can therefore be excluded from source-ownership checks without
parsing `namespace`, `section`, or declaration syntax in Python.

Private declarations are normalized to their user-facing names before namespace/name contracts are applied.

Existing Python declaration/source scans are transitional until their invariant is migrated. Do not add a new Python
regex owner scan when the compiled environment can express the same rule directly.

## Declarative architecture graphs

Repository dependency DAGs should be specified under `scripts/architecture/` rather than repeated as checker-local
`ImportBoundary` tables, layer ranks, or manual graph traversal.

The shared graph format supports:

- a primary graph whose layer data is consumed by both Python and Lean;
- `scopedImportGraphs`, each with its own source roots, layer prefixes, and upstream -> downstream edges;
- small compiled `namespaceExceptions` for intentional semantic crossings.

For an import from source layer `A` to target layer `B`, the graph rule is:

```text
A = B
or
B is an ancestor of A
```

This one rule derives downstream and sibling-import prohibitions from graph reachability.

The current SecondQuantization specification centralizes, among others:

```text
math → quantumTheory → common → {fermionic, bosonic}

Algebra → {Field, Lattice} → Transport → Validation

Semantics → Factorization → Analysis → Integration → Series

CompletedSpace → Thermal

QuantumTheory → {SingleParticle, SecondQuantization}

Combinatorics → Permutation
```

Focused Python scripts should not restate those edges. They may retain a genuinely different invariant such as exact
umbrella exposure, required physical source layout, a transitive reachability restriction stronger than direct-import
ancestry, or source syntax that is itself part of the contract.

See `scripts/architecture/README.md` for the graph schema and current scoped DAGs.

## Shared Python audit primitives

Use `architecture_audit_common.py` for repository-wide source mechanics instead of checker-local infrastructure.
The common layer provides:

- `lean_imports` / `numbered_imports` for comment-aware direct Lean imports;
- `module_matches_prefix` for module-boundary-safe prefix matching;
- `require_import` / `forbid_import_prefixes` for genuinely local individual dependency constraints;
- graph loading, module classification, reachability, and DAG validation;
- `require_files` for current canonical source owners;
- `lean_files_matching` for legacy declaration scans pending Lean migration;
- `lean_source` / `strip_lean_comments` for the shared comment-aware source view.

`ImportBoundary` / `check_import_boundaries` remain available for a local source rule that is not part of a durable
layer graph. Do not use them to create a second copy of a graph already represented under `scripts/architecture/`.

Because the full Python audit runs in one read-only process, the common layer caches deterministic file discovery,
source reads, comment-stripped Lean source, and parsed imports. Checkers should use these shared views instead of
re-reading the same tree independently when a common primitive fits the task.

Generic import parsing, module-prefix semantics, comment stripping, file scans, and dependency traversal should not be
reimplemented in individual checkers. Checker-local regexes remain appropriate only for genuinely source-level policy
that cannot be represented more robustly in the compiled Lean environment.

## One owner per architectural concern

A durable layer graph should have one authoritative specification. Focused checkers may add constraints specific to
their mathematical domain, but they should not duplicate the same dependency DAG.

For example, the fermionic responsibility graph

```text
Algebra → {Field, Lattice} → Transport → Validation
```

is owned by the shared graph specification. The AlgebraicFock, Lattice, and transport/validation checkers retain only
their non-DAG constraints.

The same one-owner rule applies across languages: once a declaration-level invariant is migrated to the compiled Lean
audit, delete the superseded Python source parser instead of keeping both as permanent guards.

## Prefer positive boundaries over exact source snapshots

Permanent audits should express the minimum durable contract. Prefer a layer graph over repeated forbidden-downstream
lists. Prefer required public umbrellas as a set over pinning their source order unless order itself is part of the
contract. This lets a layer acquire a new reusable upstream helper without turning an unrelated source snapshot into a
CI failure.

For compiled checks, prefer declaration owner, public type, namespace, or theorem contracts over implementation-body
text.

## Do not preserve migration history in permanent CI

Permanent architecture checks should not accumulate lists of files, imports, identifiers, wrappers, or helper names
that existed only before an earlier refactor. Once the current ownership/dependency invariant expresses the intended
boundary, remove the migration-specific regression guard.

A short-lived refactor branch may use a temporary migration assertion while files are being moved. It should normally
be removed before the architecture cleanup is considered complete. Keep such a guard permanently only when the old
shape remains a realistic ambiguity that cannot be expressed as a stronger current-state invariant, and document why.

Likewise, avoid checks that require exact proof fragments, helper theorem names, or implementation text unless that
syntax itself is the public contract. Prefer declaration ownership, import direction, type-level constraints, or
Lean-checked theorems when they can express the intended invariant.

## Adding a Python topology checker

1. First ask whether the rule is another edge or scoped subgraph of an existing declarative graph. If so, edit the graph
   specification instead of adding checker-local dependency logic.
2. For a genuinely distinct source-topology contract, add a focused `check_*.py` script exposing `main() -> int | None`.
3. Reuse the shared primitives in `architecture_audit_common.py`; do not add a new generic import/parser implementation.
4. Register it once in `CHECKS` in `check_architecture.py`.
5. Choose a scope for local organization only; full CI still runs every registered checker.
6. Do not add another direct workflow invocation for the checker.

If a new `check_*.py` script is intentionally *not* an architecture CI checker, add it to
`NON_ARCHITECTURE_CHECK_SCRIPTS` with that intent made explicit. Otherwise manifest validation fails.

## Adding a compiled semantic checker

1. Express the invariant as a pure `Snapshot → Array String` check in `CheckArchitecture.lean` where possible.
2. Reuse declaration/module/type helpers rather than reparsing source text.
3. Register the check in the single compiled-check array so all violations are accumulated in one run.
4. Remove any Python declaration parser that becomes redundant after the Lean check is green.
5. Keep mathematical identities in ordinary Lean theorems; architecture CI should verify the stable contract, not a
   preferred proof route.
