---
status: accepted
---

# Use Lean for semantic guarantees and source audits for architecture

Express mathematical identities and durable semantic guarantees in Lean definitions, types, and theorems. Use source architecture checks for module topology and explicit source contracts; use compiled environment audits as focused local tools for investigating elaborated API boundaries.

Declarative graphs encode allowed dependency direction, while source contracts separately encode required files or direct imports. Neither should become a catalogue of deleted paths or incidental proof syntax. The distinction permits proof refactoring while preserving the current architectural constraints.

CI combines selected source checks with Lean builds, linting, duplicate-declaration checks, and an independent `sorryAx` audit. More declaration-specific compiled architecture investigations remain local rather than becoming permanent regression checks. Source parsing cannot establish Lean semantics, and successful elaboration alone is not a substitute for rejecting proof placeholders.

Evidence: [audit responsibilities](../../scripts/architecture/README.md), [source audit entry point](../../scripts/check_architecture.py), [source topology graphs](../../scripts/architecture/source_topology.json), [fixed source contracts](../../scripts/architecture/source_contracts.json), [graph validator](../../scripts/check_architecture_graphs.py), [compiled declaration audit](../../scripts/CheckArchitecture.lean), [CI workflow](../../.github/workflows/lean_action_ci.yml), and [placeholder audit](../../scripts/CheckNoSorry.lean).

## Historical evidence

[Issue #1584](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1584) replaced source-regex ownership checks with a shared Lean-environment audit for declaration ownership and namespace/module contracts, and removed the custom SecondQuantization scope parser. The enduring boundary is that Python checks files, direct imports, dependency DAGs, reachability, and source syntax only when syntax itself is the policy; compiled Lean metadata answers declaration- and type-level questions. Exact proof bodies and helper spellings are not architecture contracts. The issue's final acceptance report records a green compiled audit, but the current [architecture handbook](../../scripts/architecture/README.md) keeps declaration-specific audit tools local unless a stable invariant is explicitly selected for CI.

[Issue #1608](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1608) made source-topology checks declarative and diagnostic: allowed dependency direction and reachability belong in DAGs, while required files, exact umbrella imports, and forbidden direct imports belong in separate source contracts. The shared primary graph uses non-overlapping module prefixes so Python and Lean classify layers consistently. Preserve independent graph diagnostics and keep forwarding-module checks to a narrow syntax contract; do not rebuild declaration or proof-body semantics in Python. The current [source-topology handbook](../../scripts/architecture/README.md) and [contract schema](../../scripts/architecture/source_contracts.json) record this split.

[Issue #554](https://github.com/naoki-cpp/LeanCondensedMatter/issues/554) added a permanent mode-boundary audit: foundational finite-support occupation/Fock modules may not regain `[Fintype Mode]` or `[Finite Mode]`, the root mode-label type stays assumption-free, and the unused `modeCount` declaration remains absent. The guard protects the algebraic/finite-analytic boundary instead of broadly banning legitimate downstream finite sums and Hilbert transports.

[Issue #553](https://github.com/naoki-cpp/LeanCondensedMatter/issues/553) added a repository-wide source audit for public real-valued physical definitions that directly project `.re`, while allowing proof-local extraction after a reality theorem and private implementation details. Declaration-specific exceptions require a rationale and stale exceptions fail the check; the resulting current allowlist is empty. This guard protects scalar semantics in addition to compiled theorem correctness.

[Issue #535](https://github.com/naoki-cpp/LeanCondensedMatter/issues/535) addressed `unusedArguments` under `--wfail` by omitting unnecessary `[DecidableEq]` parameters from public declarations and placing `classical` only in proofs that need equality decisions. It chose to fix the API boundary rather than suppress the warning globally, preventing unrelated full rebuilds from failing on automatically propagated instance arguments.

[Issue #525](https://github.com/naoki-cpp/LeanCondensedMatter/issues/525) treats lint exceptions as API signals to review rather than debt to delete mechanically. A targeted `unusedArguments` suppression can record an erased summability or integrability witness on a totalized function, while `simpNF` edits can change canonical rewrite behavior. Such exceptions should remain narrow and explained until the interface is deliberately changed; semantic cleanup is split by family and validated for proof churn.

[Issue #513](https://github.com/naoki-cpp/LeanCondensedMatter/issues/513) made repository-wide `lake lint` a CI gate only after clearing the existing warning baseline. It separated mechanical cleanup from semantic review: `simpNF` changes were audited because they can alter simplifier behavior, while genuinely necessary unused arguments require narrow justified suppressions. A project-wide check should be enabled after its findings are resolved, not added over a known failing baseline.

[Issue #352](https://github.com/naoki-cpp/LeanCondensedMatter/issues/352) made the architecture contract executable: Common may not depend on Fermionic or Bosonic, and Analysis/Combinatorics may not depend on SecondQuantization. The lasting guard is this present dependency graph and canonical public entry point. Checks should enforce semantic ownership and allowed layering; permanent blacklists of incidental retired paths are not the design contract.

[Issue #433](https://github.com/naoki-cpp/LeanCondensedMatter/issues/433) uses explicit low-order theorem corollaries as readable regression checks for factorial normalization, disconnected-term cancellation, and agreement between the formal and analytic linked-cluster results. Keep these checks at the public mathematical boundary so convention drift is visible in theorem statements, while the general theorem remains the source of the result.

[PR #2](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2) made the absence of proof placeholders a CI requirement, explicitly tying the word “proved” to compilation without `sorry`. Its first implementation searched source text. The enduring decision is the proof-completeness requirement; the current compiled `sorryAx` audit is the relevant enforcement mechanism, so the original text-search command is not a compatibility requirement.
