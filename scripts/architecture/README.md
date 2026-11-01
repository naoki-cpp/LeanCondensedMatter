# Architecture checks

Architecture checks describe the repository's current dependency and ownership boundaries. They are
not a history of previous module layouts.

## Execution

Pull-request CI keeps the blocking path small and selects source-topology and compiled checks
independently:

```text
source-topology change                  Lean library / build-input change
        ↓                                           ↓
Python source audit                              lake build --wfail
files / direct imports / DAGs / reachability             ↓
/ narrow source rules                         duplicate declaration audit
                                               / sorryAx audit / lake lint
```

Ordinary Lean library changes normally exercise both branches. Source-audit-only tooling does not
force a library build, while advisory theorem-catalog tooling remains outside the pull-request gate.
On `main`, advisory-tooling changes may request a build cache so the separate Lean Insights workflow
can run against the merged commit.

Run the source audit with:

```bash
python3 scripts/check_architecture.py
```

Focused local scopes are available as `--scope core` and `--scope second-quantization`.

After a successful build, two compiled architecture tools are available for focused local work:

```bash
lake env lean scripts/CheckSemanticBoundaries.lean
lake env lean scripts/CheckArchitecture.lean
```

`CheckSemanticBoundaries.lean` checks elaborated public declaration types for broad properties such
as dimension independence and forbidden upward dependencies. It is deliberately local-only: these
checks are useful while reviewing or carrying out a refactor, but they do not become bespoke CI
regression machinery.

`CheckArchitecture.lean` handles more declaration-specific questions such as exact ownership,
namespace routing, and bridge-specific type-shape checks. It is also intentionally not part of the
pull-request gate.

Other compiled checks can be run locally as needed:

```bash
lake env lean scripts/CheckNoSorry.lean
lake lint
```

## Direct import hygiene

The primary source audit also checks every project Lean source file, including
`LeanCondensedMatter.lean`, for duplicate *identical import commands*, imports of the
module itself, and direct imports of project modules without a matching source file.
Import modifiers remain significant: for example, `public import A` together with
`import all A` is not a duplicate command and can be intentional.

A directly imported module can be transitively reachable through another import and still
be an intentional source-level dependency. Likewise, `public import` may be required to
expose a signature. Do not treat graph reachability as proof of an unnecessary import:
review candidates with Lean's import analysis tools and compile the module and consumers
before removing an import or changing its visibility. This audit does not enforce a fixed
import count, disallow all public imports, or attempt to minimize Mathlib imports automatically.

### Advisory transitive overlap report

For manual import reduction, reuse the documentation site's existing project-module
import graph exporter. CI runs the same read-only report, but a nonempty report does not
fail the build:

```bash
python3 scripts/export_module_import_graph.py --report-overlaps --limit 30
```

The report puts module-system files first and shows when one *project-local* direct
import is also transitively reachable through another direct project import. Import-only
umbrella files (a matching subtree, with only import commands, documentation, and the
standard header option) are **counted separately and hidden from the default review
list**. Run with `--include-umbrellas` to show them for diagnostics. Other files are
marked `[review]`, **not** "redundant" or "safe to delete". An implementation may
intentionally import a direct owner despite also reaching it through another module.
This source-only classification is conservative and does not infer public visibility,
declaration usage, or Mathlib's internal graph. The ordinary JSON export is unchanged.

Review each candidate with Lean's own import tools. In a temporary edit of an
already-migrated `module` file, add `meta import ImportGraph.Tools.NormImports`
and invoke `#norm_imports` to inspect import-block normalization, then undo the
temporary diagnostic import. The tool preserves the required visibility and phase
of the available imports, but not all intentional source-level ownership choices.
For declaration-level minimum-import investigations, use the relevant Lean tools
with their documented syntax/tactic limitations. Finally, compile the edited file
and its downstream consumers before deleting or narrowing any direct import.
Legacy non-module files require a separate review: `#norm_imports` does not support
them yet. Do not change imports just to eliminate every overlap warning.

## Declarative source topology

`check_architecture_graphs.py` owns dependency direction and reachability. Its data lives here:

- `second_quantization.json` — the shared primary layer graph and SecondQuantization-focused DAGs;
- `source_topology.json` — Transport, current, LinearResponse, Gibbs/entropy, and other source DAGs;
- `ahe_topology.json` — Massive-Dirac Model/Intrinsic and Bastin stage DAGs.

Edges are written **upstream -> downstream**. A source layer may import itself or an ancestor. Scoped
DAGs may use `coveragePrefixes` when every source module in a subtree must be classified.

The primary graph is also consumed by the optional compiled `CheckArchitecture.lean` audit, so its
module prefixes must form a non-overlapping partition. Python checks this before the build.

## Fixed source contracts

`source_contracts.json` contains concrete source topology that is not implied by an allowed DAG
edge, such as:

- required canonical files or directories;
- required or exact direct imports;
- forbidden direct imports or import prefixes.

An allowed dependency direction and a required direct edge are different contracts. Do not encode a
required edge merely by adding a DAG edge. Retired-path absence is not a CI contract: removing a file
does not create a permanent rule that the old path may never exist again.

## Source versus compiled semantics

Python owns properties of repository source topology. It parses Lean imports, but it is not a Lean
semantic parser. Source syntax should be inspected only when syntax or layout is itself the invariant.
Focused Python checkers are reserved for rules that do not fit the uniform graph or source-contract
data shapes, such as exact public-umbrella import boundaries where an umbrella shares a module prefix
with its implementation subtree. They must not freeze retired paths or proof-stage directory layouts.
Only checkers explicitly listed in `check_architecture.py` participate in CI; a local
`check_*.py` script is not enrolled automatically.

Lean owns properties of the elaborated environment. `CheckSemanticBoundaries.lean` provides a
focused local view of broad public-type boundaries, while `CheckArchitecture.lean` provides a more
routing-sensitive local audit. Neither is a permanent CI regression guard.

`CheckNoSorry.lean` independently rejects any project declaration whose axioms contain `sorryAx` and
remains part of CI. Mathematical identities and durable semantic guarantees should be expressed in
ordinary Lean definitions, types, and theorems when possible rather than architecture scripts.

## Adding or changing a rule

Choose one authoritative mechanism:

1. dependency direction or reachability -> an existing architecture DAG;
2. a required current file, directory, or direct import -> `source_contracts.json`;
3. a broad elaborated public-type investigation for a focused refactor -> `CheckSemanticBoundaries.lean`;
4. a declaration-level ownership or routing investigation for a focused refactor -> `CheckArchitecture.lean`;
5. a genuinely distinct source layout or syntax invariant -> a focused Python checker.

Reuse `architecture_audit_common.py` and `architecture_graph_scopes.py` for shared source mechanics.
Do not turn a one-off historical absence or refactor-specific expectation into a new CI regression
check. Prefer Lean theorems or type-level guarantees for semantic invariants that must be durable.
