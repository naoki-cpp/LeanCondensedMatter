# Analysis audit against Mathlib 4.31

This document records the result of issue #281's audit of `LeanCondensedMatter/Analysis` against the repository-pinned Mathlib revision (`v4.31.0`). It is the stable mapping table requested by Phase 0 of the tracking issue.

The classifications used here are:

- **Mathlib replacement**: project code was deleted or rewritten around an existing Mathlib declaration.
- **Thin retained corollary**: the project statement remains because it crosses useful type or namespace boundaries, but its proof delegates to Mathlib.
- **Project-specific**: no suitable pinned-Mathlib replacement exists.
- **Upstream candidate**: the statement is general-purpose and should eventually be proposed to Mathlib after its signature stabilizes.

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
| `tsum_norm_sq_orthogonalProjectionOnto_eq_finrank` | finite-dimensional trace APIs are not directly applicable because the ambient Hilbert space may be infinite-dimensional | Project-specific | Proof shortened with the generic Parseval corollary in #314. |
| `ContinuousLinearMap.eigenvectorHilbertBasis` | `HilbertBasis.mk` accepts orthonormality plus density directly | Project-specific with Mathlib-shortened proof | Refactored in #321; the density transport remains specific to the project construction. |

All five Section B spikes were completed; `eigenvalueScaleEquiv` is recorded in the previous table because it became a direct replacement.

## Project-specific infrastructure retained

### Ordered-simplex integration and shuffles

The six analysis modules remain project-specific:

```text
Integral → Calculus → ShuffleIntegral → BinaryShuffle → BinarySlotShuffle → FamilyShuffle
```

The dependency audit found that the chain itself was already one-way. PR #322 removed the actual reverse dependency from `Combinatorics/FamilySlotShuffle` to the analysis layer. PRs #323 and #325 moved ordered-simplex-independent shuffle infrastructure into `Combinatorics`. The remaining cast, continuity, recursive integral, and shuffle identities are retained as ordered-simplex-specific API.

### Continuous functional calculus on eigenvectors

`Polynomial.aeval_apply_eigenvector` and `cfc_apply_eigenvector` remain useful project API. Mathlib 4.31 provides the algebraic core for polynomial evaluation but not the exact mixed-scalar continuous-functional-calculus theorem needed here.

### Compact self-adjoint spectral packaging

`EigenvectorIndex`, `eigenvectorFamily`, countability, the Hilbert-basis construction, and `tsum` reconstruction remain project-specific. Mathlib supplies substantial building blocks but not this complete packaging.

### Spectral trace and Hilbert–Schmidt operators

The repository does not yet implement Mathlib's general trace-class operator ideal. PR #327 introduced the precise canonical names

```lean
ContinuousLinearMap.HasSummableRealEigenvalues
ContinuousLinearMap.spectralTrace
```

while retaining `IsTraceClass` and `trace` as compatibility aliases. PRs #329, #331, and #333 added the bundled compatibility layer

```lean
ContinuousLinearMap.SpectralTraceClass T
```

for compactness, symmetry, and spectral summability. PR #335 added the one-way bridge from `QuantumTheory.TraceClass.DensityOperator` to that bundled API. Existing physics-facing theorem statements remain unchanged.

The project-local Hilbert–Schmidt predicate, basis-independence proofs, inner product, and reconciliation with the spectral trace remain project-specific at the pinned revision.

### Peierls–Bogoliubov

The Peierls–Bogoliubov inequality and Gibbs specialization remain project-specific. Only the one-use affine CFC wrapper was removed.

## Upstream candidates

The following declarations are still candidates for Mathlib after their signatures and proof costs are stabilized:

- `Finsupp.hasSum_prod_nonneg`;
- `Finsupp.hasSum_prod`;
- `Finsupp.hasSum_prod_geometric`;
- `tsum_fiberwise_eq_of_summable`;
- `HilbertBasis.hasSum_norm_sq_inner`.

The injective nonnegative subseries helper is no longer an upstream candidate because its sole project use is expressed directly by existing Mathlib APIs.

## Remaining technical debt

`Analysis/InfiniteSum/FinsuppProduct.lean` still uses unbounded heartbeats for its two finite-cardinality induction proofs. Before upstreaming, the proof should be restructured so that:

1. each induction step elaborates under the default heartbeat budget;
2. imports are reduced to the actual owner modules;
3. the statements are generalized only where the generalized form has a clear use;
4. the geometric specialization remains a small corollary of the general product theorem.

## Compatibility and validation status

The completed refactors preserve the public theorem statements used by `QuantumTheory`, `SecondQuantization`, and the current roadmap exit theorems. The associated PRs report passing Lean Action CI, warning-as-error/no-`sorry` checks, and Theorem Catalog validation.

This document records repository-local audit results only. Any future Mathlib PR must be checked again against the then-current Mathlib API and contribution conventions.
