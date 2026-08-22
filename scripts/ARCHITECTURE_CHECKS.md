# Architecture checks

`check_architecture.py` is the single CI entry point for the repository's Python architecture checks.
Individual checker scripts remain focused executables, but workflows do not enumerate them directly.

## Execution scopes

The runner exposes two CI partitions:

- `core`: repository-wide, QuantumTheory, transport, single-particle, and combinatorics checks;
- `second-quantization`: SecondQuantization-specific ownership and dependency checks.

Scopes are execution partitions only. They do not define or override the Lean module dependency graph.
Each checker is registered exactly once, so workflow partitioning cannot accidentally execute the same audit twice.
The runner also rejects unregistered `check_*.py` scripts except for explicitly listed non-architecture utilities.

Run all checks locally with:

```bash
python3 scripts/check_architecture.py
```

Run one CI partition with:

```bash
python3 scripts/check_architecture.py --scope core
python3 scripts/check_architecture.py --scope second-quantization
```

List registered checks without executing them with:

```bash
python3 scripts/check_architecture.py --list
```

## What belongs in architecture CI

Architecture CI encodes the repository's **current structure**, not the sequence of refactors that produced it.
Durable invariants include:

- dependency direction between layers;
- canonical ownership of public abstractions;
- representation-independent code staying upstream of concrete realizations;
- foundational APIs remaining free of accidental finiteness assumptions;
- terminal validation/example layers not being imported by reusable theory;
- mathematically lossy implementation patterns that the project intentionally forbids.

These checks describe *what must remain true*, not *how a proof happens to be written today*.

## Shared audit primitives

Use `architecture_audit_common.py` for repository-wide mechanics instead of checker-local infrastructure.
The common layer provides:

- `lean_imports` / `numbered_imports` for comment-aware direct Lean imports;
- `module_matches_prefix` for module-boundary-safe prefix matching;
- `require_import` / `forbid_import_prefixes` for individual dependency edges;
- `ImportBoundary` / `check_import_boundaries` for declarative source-tree dependency rules;
- `require_files` for current canonical owners;
- `lean_files_matching` for declaration ownership scans;
- `strip_lean_comments` for the shared comment-aware source view.

A checker should declare its layer graph as data where possible. For example:

```python
DEPENDENCY_BOUNDARIES = (
    ImportBoundary(
        COMMON,
        (FERMIONIC_PREFIX, BOSONIC_PREFIX),
        "Common must remain statistics-independent",
    ),
)
```

Generic import parsing, module-prefix semantics, comment stripping, file scans, and dependency traversal should not be
reimplemented in individual checkers. Checker-local regexes remain appropriate for genuinely domain-specific
declarations or semantic tokens.

## One owner per architectural concern

A durable layer graph should have one authoritative checker. Focused checkers may add constraints specific to their
mathematical domain, but they should not duplicate the same repository-wide dependency DAG.

For example, the fermionic responsibility graph

```text
Algebra → {Field, Lattice} → Transport → Validation
```

is owned by the transport/validation boundary checker. The AlgebraicFock and Lattice checkers retain their own
finite-dimensionality, namespace, and response-separation rules without maintaining a second copy of that DAG.

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

## Adding a checker

1. Add the focused `check_*.py` script.
2. Reuse the shared primitives in `architecture_audit_common.py`; do not add a new generic import/parser implementation.
3. Register it once in `CHECKS` in `check_architecture.py`.
4. Choose the execution scope based on CI cost and ownership, not dependency direction.
5. Do not add another direct workflow invocation for the checker.

If a new `check_*.py` script is intentionally *not* an architecture CI checker, add it to
`NON_ARCHITECTURE_CHECK_SCRIPTS` with that intent made explicit. Otherwise manifest validation fails.
