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

After a successful build, additional compiled analysis is available locally when a refactor needs it:

```bash
lake env lean scripts/CheckArchitecture.lean
lake env lean scripts/CheckNoSorry.lean
lake lint
```

`CheckArchitecture.lean` is intentionally not part of the pull-request gate. Declaration-by-declaration
ownership and semantic routing checks are useful during focused refactors, but they should not turn
past layouts into permanent CI regression guards.

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

Lean owns properties of the elaborated environment. The optional `CheckArchitecture.lean` audit can
inspect canonical owners, module/namespace relationships, declaration-type dependencies,
dimension-independent signatures, and typed semantic bridges. Private declarations are normalized
to their user-facing names before namespace checks.

`CheckNoSorry.lean` independently rejects any project declaration whose axioms contain `sorryAx` and
remains part of CI. Mathematical identities belong in ordinary Lean theorems rather than architecture
scripts.

## Adding or changing a rule

Choose one authoritative mechanism:

1. dependency direction or reachability -> an architecture DAG;
2. a required current file, directory, or direct import -> `source_contracts.json`;
3. a declaration-level semantic investigation for a focused refactor -> `CheckArchitecture.lean`;
4. a genuinely distinct source layout or syntax invariant -> a focused Python checker.

Reuse `architecture_audit_common.py` and `architecture_graph_scopes.py` for shared source mechanics.
Add a focused checker to `check_architecture.py` only when it expresses a durable CI invariant.

Prefer structural invariants over path-by-path regression guards. Do not duplicate the same invariant
across checkers or freeze proof-helper choices as CI policy.
