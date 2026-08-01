# Analysis audit against Mathlib 4.31

This document records the result of issue #281's audit of `LeanCondensedMatter/Analysis` against the repository-pinned Mathlib revision (`v4.31.0`). It is the stable declaration-to-Mathlib mapping requested by Phase 0 of the tracking issue and reflects the canonical API after PR #340.

The classifications used here are:

- **Mathlib replacement**: project code was deleted or rewritten around an existing Mathlib declaration.
- **Thin retained corollary**: the project statement remains because it crosses useful type or namespace boundaries, but its proof delegates to Mathlib.
- **Project-specific**: no suitable pinned-Mathlib replacement exists.
- **Upstream candidate**: the statement is general-purpose and may be proposed to Mathlib after its signature and proof cost stabilize.

Backward compatibility is not a constraint for the remaining #281 work. The repository now prefers one canonical API and migrates all in-repository callers in the same focused PR.

## Direct replacements and localized wrappers

| Project declaration | Mathlib basis | Classification | Action |
|---|---|---|---|
| `ContinuousLinearMap.real_smul_eq_complex_smul` | scalar simplification after extensionality | Mathlib replacement | Deleted in #283; the only call site now uses local simplification. |
| `cfc_affine` | `cfc_add`, `cfc_const`, `cfc_smul_id` | Mathlib replacement | Deleted in #284 and expanded at its only use. |
| `Combinatorics.BinaryShuffle.orderedSimplexIntegral_cast` | direct dependent transport | Redundant compatibility alias | Moved to the owner namespace in #288, then the old alias was deleted in #301. |
| `eigenvalueScaleEquiv` | `Equiv.mulLeft₀` and `Equiv.subtypeEquiv` | Mathlib replacement | Replaced in #293; the remaining equivalence is implementation-local. |
| `inner_mul_inner_conj_eq_norm_sq` | `inner_conj_symm`, `Complex.mul_conj`, `Complex.normSq_eq_norm_sq` | Thin retained corollary | Kept private in `TraceClass/Ops.lean` by #296 because it has three local uses. |
| `HilbertBasis.hasSum_norm_sq_inner` | `HilbertBasis.hasSum_inner_mul_inner` plus `Complex.reCLM` | Thin retained corollary / upstream candidate | Extracted to `Analysis/InnerProductSpace/HilbertBasisParseval.lean` in #297. |
| `tsum_le_tsum_of_injective_of_nonneg` | `Summable.comp_injective`, `hasSum_le_inj` | Mathlib replacement | Deleted and inlined at its only use in #300. |
| `tsum_fiberwise_eq_of_summable` | `Summable.prod_symm`, `Equiv.prodComm.tsum_eq`, `HasSum.prod_fiberwise` | Thin retained corollary / upstream candidate | Extracted to `Analysis/InfiniteSum/Fiberwise.lean` in #292. |

## Compile-spike results

| Project declaration | Pinned-Mathlib result | Classification | Action |
|---|---|---|---|
| `Polynomial.aeval_apply_eigenvector` | `Polynomial.aeval_eq_aeval_map`, `Polynomial.map_aeval_eq_aeval_map`, `Module.End.aeval_apply_of_mem_apply_eq_smul` | Thin retained corollary | Proof shortened in #305; the statement still bridges real polynomials, complex operators, and continuous linear maps. |
| `ContinuousLinearMap.eigenspace_smul` | `Module.End.eigenspace_div` | Thin retained corollary | Proof shortened in #313; the semantic project statement remains. |
| `eigenvalueScaleEquiv` | `Equiv.mulLeft₀`, `Equiv.subtypeEquiv` | Mathlib replacement | Replaced in #293 and made implementation-local. |
| `tsum_norm_sq_orthogonalProjectionOnto_eq_finrank` | finite-dimensional trace APIs are not directly applicable because the ambient Hilbert space may be infinite-dimensional | Project-specific | Proof shortened with the generic Parseval corollary in #314. |
| `ContinuousLinearMap.eigenvectorHilbertBasis` | `HilbertBasis.mk` accepts orthonormality plus density directly | Project-specific with Mathlib-shortened proof | Refactored in #321; the density transport remains specific to the project construction. |

## Project-specific infrastructure retained

### Ordered-simplex integration and shuffles

The six analysis modules remain project-specific:

```text
Integral → Calculus → ShuffleIntegral → BinaryShuffle → BinarySlotShuffle → FamilyShuffle
```

The dependency audit found that this chain was already one-way. PR #322 removed the actual reverse dependency from `Combinatorics/FamilySlotShuffle` to the analysis layer. PRs #323 and #325 moved empty-family shuffle structure and ordered-simplex-independent integrands into `Combinatorics`. No additional project-local generic interval-integral theorem needed extraction. The remaining cast, continuity, recursive integral, and shuffle identities are retained as ordered-simplex-specific API.

### Continuous functional calculus on eigenvectors

`Polynomial.aeval_apply_eigenvector` and `cfc_apply_eigenvector` remain useful project API. Mathlib 4.31 provides the algebraic core for polynomial evaluation but not the exact mixed-scalar continuous-functional-calculus theorem needed here.

### Compact self-adjoint spectral packaging

`EigenvectorIndex`, `eigenvectorFamily`, countability, the Hilbert-basis construction, and `tsum` reconstruction remain project-specific. Mathlib supplies substantial building blocks but not this complete packaging.

### Spectral trace and Hilbert–Schmidt operators

The repository does not implement Mathlib's general trace-class operator ideal. Its unbundled spectral data use the precise names

```lean
ContinuousLinearMap.HasSummableRealEigenvalues
ContinuousLinearMap.spectralTrace
```

and the canonical public operator hypothesis is

```lean
ContinuousLinearMap.SpectralTraceClass T
```

which bundles compactness, symmetry, and spectral summability.

PR #327 introduced the precise spectral names. PRs #329, #331, and #333 built the bundled API. PR #335 initially added a one-way density-operator bridge. After the compatibility policy changed, PR #338 made `SpectralTraceClass` the object stored directly by infinite-dimensional density operators and deleted the bridge module. PR #340 then removed the misleading `ContinuousLinearMap.IsTraceClass` and unbundled `ContinuousLinearMap.trace` compatibility aliases, renamed scalar/additive/cyclic theorems to spectral-trace terminology, and migrated all repository callers.

The concise projection `h.trace` on a `SpectralTraceClass` value remains because its receiver fixes the spectral-trace meaning; it is not an alias for a general operator trace.

The project-local Hilbert–Schmidt predicate, basis-independence proofs, inner product, and reconciliation with `spectralTrace` remain project-specific at the pinned revision.

### Peierls–Bogoliubov

The Peierls–Bogoliubov inequality and Gibbs specialization remain project-specific. Only the one-use affine CFC wrapper was removed.

## Canonical API status after #340

The following compatibility-only surfaces have been removed rather than deprecated:

- `ContinuousLinearMap.IsTraceClass`;
- unbundled `ContinuousLinearMap.trace`;
- the density-operator spectral-trace bridge module;
- the compatibility-only fermionic formal-log partition-function module;
- raw crossing-pair and `% 2`-specific perfect-pairing wrappers superseded by normalized and general APIs.

Repository callers now use `HasSummableRealEigenvalues`, `spectralTrace`, `SpectralTraceClass`, `PowerSeries.normalizeByConstantCoeff`, `PowerSeries.logOf`, normalized pairing data, and the general `Nat.ModEq` theorem as appropriate.

## Upstream candidates

The following declarations remain candidates for Mathlib after their signatures and proof costs are stabilized:

- `Finsupp.hasSum_prod_nonneg`;
- `Finsupp.hasSum_prod`;
- `Finsupp.hasSum_prod_geometric`;
- `tsum_fiberwise_eq_of_summable`;
- `HilbertBasis.hasSum_norm_sq_inner`.

The injective nonnegative subseries helper is no longer an upstream candidate because its sole project use is expressed directly by existing Mathlib APIs.

The upstream work may be tracked separately rather than blocking closure of #281.

## Remaining repository technical debt

`Analysis/InfiniteSum/FinsuppProduct.lean` still uses `set_option maxHeartbeats 0` for two finite-cardinality induction proofs:

- `hasSum_prod_nonneg_fin`;
- `hasSum_prod_fin`.

Before upstreaming the Finsupp results, these proofs should be restructured so that:

1. each theorem elaborates under the default heartbeat budget;
2. repeated `Option`-product and `Fin`-successor reindexing steps are isolated where that reduces elaboration cost;
3. imports are reduced to their actual owner modules;
4. the geometric specialization remains a small corollary of the general product theorem.

## Validation status

The completed focused PRs report passing Lean Action CI, warning-as-error and no-`sorry` checks, and Theorem Catalog validation. PR #340 validated the repository after removing the legacy trace and compatibility APIs.

Closing #281 still requires removing the unbounded heartbeat settings, validating the resulting repository build, and confirming that this document remains synchronized with the final canonical API.

This document records repository-local audit results only. Any future Mathlib PR must be checked again against the then-current Mathlib API and contribution conventions.
