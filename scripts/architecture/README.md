# Architecture checks

Architecture checks describe the repository's current dependency and ownership boundaries. They are
not a history of previous module layouts.

## Execution

Pull-request CI keeps the blocking path small:

```text
Python source audit
  files / direct imports / DAGs / reachability / narrow layout rules
        ↓
lake build --wfail
        ↓
duplicate declaration audit / sorryAx audit / lake lint
```

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
data shapes. Only checkers explicitly listed in `check_architecture.py` participate in CI; a local
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
