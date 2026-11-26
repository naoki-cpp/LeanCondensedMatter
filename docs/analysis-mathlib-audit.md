# Analysis inventory against Mathlib 4.35

Current mapping between project analysis infrastructure and the repository-pinned Mathlib revision
`v4.35.0`. This document describes the present API, not the sequence of refactors that produced it.

## Classification

- **Mathlib-owned:** the project uses the Mathlib declaration directly.
- **Thin project corollary:** a small wrapper crosses a useful scalar, coercion, or namespace boundary.
- **Project-specific:** no pinned-Mathlib declaration provides the required theorem or packaging.
- **Upstream candidate:** general-purpose project code that may be suitable for Mathlib.

## Mathlib-owned foundations

The project uses Mathlib directly for:

- bounded and compact continuous linear maps;
- compactness under bounded composition through `IsCompactOperator.comp_clm` and `IsCompactOperator.clm_comp`;
- positivity under adjoint conjugation through `ContinuousLinearMap.IsPositive.conj_adjoint`;
- finite-dimensional matrix trace and orthonormal-basis formulas;
- Hilbert-basis norm-square Parseval via `lp.hasSum_norm` and `HilbertBasis.repr_apply_apply`;
- finite-dimensional determinants through `ContinuousLinearMap.det`;
- infinite products through `HasProd`, `Multipliable`, and `tprod`;
- convergence of `∏' i, (1 + coeff i)` from `Summable (fun i => ‖coeff i‖)` through
  `multipliable_one_add_of_summable`;
- self-adjoint operator spectrum and eigenspaces;
- continuous functional calculus on C⋆-algebras;
- Bochner integration and interval integrals;
- power series and elementary complex/real analysis;
- general incidence algebras and Möbius inversion;
- polynomial evaluation on eigenvectors through `Module.End.aeval_apply_of_mem_apply_eq_smul`;
- scalar eigenspace transport through `Module.End.eigenspace_div`.

Project modules must not duplicate these APIs under compatibility names.

## Thin retained corollaries

The following remain because their statements match recurring project boundaries:

| Project declaration | Mathlib basis | Purpose |
|---|---|---|
| `cfc_apply_eigenvector` | continuous functional calculus and spectral mapping | Evaluate a continuous scalar function on an eigenvector. |

## Project-specific infinite-sum infrastructure

`Analysis/InfiniteSum/` owns:

- finite products of summable series indexed by `Finsupp`;
- geometric product specializations.

Fiberwise sums use `Equiv.prodComm`, `Equiv.hasSum_iff`, and `HasSum.prod_fiberwise`
directly. Strict comparison with a proper subseries uses Mathlib's subtype/complement sum
identity and positivity of the omitted subseries.

These modules are physics-independent.

The diagonal Fredholm slice reuses Mathlib's infinite-product convergence and reindexing APIs
directly. No new generic infinite-product theorem was needed for the current vertical slice.

## Project-specific compact spectral packaging

Mathlib supplies eigenspaces and compact-operator primitives but not the complete package required by
the repository. `Analysis/Operator/Spectral/` provides:

- the nonzero real eigenvalue index with multiplicity;
- a countable orthonormal eigenvector family;
- reconstruction of compact self-adjoint operators;
- kernel/orthogonal-complement decomposition;
- Hilbert-basis comparison theorems.

## Trace-class APIs

`ContinuousLinearMap.IsTraceClass T` is the project-local general non-self-adjoint trace-class
membership predicate. It is defined by Hilbert--Schmidt membership of
`CFC.sqrt (CFC.abs T)` and is equivalent, in every Hilbert basis, to summability of the
nonnegative diagonal of `|T|`.

The compact self-adjoint spectral specialization remains

```lean
ContinuousLinearMap.SpectralTraceClass T
```

which bundles general trace-class membership and symmetry. Compactness is derived from
`IsTraceClass.isCompact`, and summability of the nonzero real eigenvalues is derived from the
compact self-adjoint characterization. Its associated `spectralTrace` is the real spectral sum.

`Analysis/Operator/TraceClass/General.lean` owns general membership, the Hilbert-basis criterion,
the canonical trace norm, and its diagonal and polar-factor formulas.
`Analysis/Operator/TraceClass/Trace.lean` owns the characterization `T = A† B`,
the bound `‖T‖₁ ≤ (‖A‖²_HS + ‖B‖²_HS) / 2`, the sharp factorization with both squared
Hilbert--Schmidt norms equal to the trace norm, and compactness, together with the direct diagonal
`Summable`/`HasSum`/`tsum` API, basis independence, and the canonical complex trace.
`Analysis/Operator/TraceClass/Ops.lean` owns additive/scalar/adjoint closure, bounded left/right
ideal closure, complex-trace linearity and cyclicity, adjoint-conjugation invariance, and the
corresponding trace-norm identities, ideal bounds, triangle inequality, and trace modulus bound.
`Analysis/Operator/TraceClass/Spectral.lean` owns spectral summability, the bundled
self-adjoint specialization, spectral trace identities, and the compact self-adjoint characterizations
of general trace-class membership, trace norm, and complex trace.

`Analysis/Operator/Diagonal.lean` owns the neutral Hilbert-basis diagonal construction, including
the absolutely summable rank-one series, basis action, and compactness.

The basis-independent general complex trace is `IsTraceClass.trace`. For self-adjoint
trace-class operators, `IsTraceClass.realTrace` transports that proved-real scalar losslessly to
`ℝ` through `Complex.selfAdjointEquiv`. The real-valued `spectralTrace` remains the
eigenvalue-sum representation for compact self-adjoint operators rather than the canonical trace API.
On the overlap, `IsTraceClass.trace_eq_spectralTrace` identifies the general complex trace with the
coercion of that spectral sum to `ℂ`.

## Hilbert–Schmidt API

`Analysis/Operator/HilbertSchmidt/` contains the project-local Hilbert–Schmidt predicate,
basis-independence results, adjoint and bounded-composition closure, compactness, inner product, and
trace reconciliation used by current proofs. No pinned-Mathlib replacement covers the same package.

The package supplies the neutral norm-square series used by general trace-class membership together
with the Hilbert--Schmidt inner product used to prove absolute convergence and basis independence of
the general complex trace. The general trace-class layer builds on this package for adjoint and
bounded-composition closure, the left/right ideal norm bounds, and cyclicity of the canonical
complex trace; completeness remains a separate downstream result.

## Diagonal Fredholm determinant API

`Analysis/Operator/Fredholm.lean` provides the project-specific interpretation of Mathlib's
infinite product as a Fredholm determinant for explicit diagonal data:

```lean
Fredholm.diagonalDet coeff = ∏' i, (1 + coeff i).
```

The module reuses Mathlib for convergence, reindexing of `tprod`, finite-product reduction, and
nonvanishing of absolutely convergent products. Project-specific theorems connect the coefficient
family to `HilbertBasis.diagonalOp`, including the action of `1 + diagonalOp b coeff` on basis vectors
and the nonzero kernel vector produced by a coefficient equal to `-1`.

This is a genuine infinite-dimensional diagonal slice. It is not a determinant on arbitrary compact,
normal, or trace-class operators and is not independent of unrelated diagonal presentations.

`Mathlib.Topology.Algebra.Module.Determinant` provides `ContinuousLinearMap.det` as the determinant of
the underlying linear endomorphism. It is appropriate only for future finite-dimensional
compatibility results and is not used as the infinite-dimensional definition.

A general Fredholm determinant still requires trace-class approximation/completeness and a
convergent presentation-independent determinant construction. The scoped dependency graph is
recorded in `docs/roadmaps/fredholm-determinant.md`.

## Ordered-simplex and Dyson analysis

The ordered-simplex integral and shuffle modules remain project-specific. Their dependency direction
is from combinatorial shuffle data toward analysis, never from generic combinatorics into physical
modules.

`Analysis/Dyson/` owns the generic Banach-algebra Dyson recursion, factorial estimates, convergence,
Volterra equation, uniqueness, and constant-generator exponential theorem. Finite and quantum
specializations reuse this layer.

## Continuous functional calculus applications

The project-specific eigenvector and compactness lemmas support:

- the entropy operator `-ρ log ρ`;
- the Gibbs operator `exp (-βH)`;
- the Peierls–Bogoliubov inequality.

The base Mathlib continuous-functional-calculus instance may need to be enabled locally in consuming
modules.

## Upstream candidates

Current general-purpose candidates include:

- `Finsupp.hasSum_prod_nonneg`;
- `Finsupp.hasSum_prod`;
- `Finsupp.hasSum_prod_geometric`.

Each candidate must be rechecked against the then-current Mathlib API before submission.

## Mathlib 4.35 API overlap assessment

The following checks distinguish genuinely new Mathlib APIs from older primitives already
used in local proofs. A similarly named theorem is not enough to justify deleting a
canonical project API; the statements, hypotheses, and in-repository consumers must agree.

| Mathlib 4.35 API | Project area | Current disposition |
|---|---|---|
| `Finset.prod_extend`, `Finset.prod_extend_one_of_injective`, `Finset.prod_eq_prod_extend` | `Combinatorics/Common/FintypeProduct` and finite-product factorization clients | **Inspect as a possible simplification**, not a direct deletion: the new results extend functions along injections with a unit default, while `Fintype.prod_equiv_sigma` reindexes an equivalence and splits a dependent sum. |
| `List.Interleaves` and its order lemmas | `Combinatorics/Common/ListFlatMapOrder` and shuffle/order modules | **Different interface**: interleaving two lists with a relation is not automatically the ordering of arbitrary blocks of a duplicate-free `List.flatMap`. A reusable bridge would be needed before dropping the existing theorems. |
| `lp.hasSum_norm`, `HilbertBasis.repr_apply_apply` | Hilbert-basis Parseval | **Use directly**: the Hilbert basis representation is a linear isometric equivalence with `ℓ²`; its norm-square sum is Mathlib's `lp.hasSum_norm` at `p = 2`. Consumers normalize inner-product orientation with `norm_inner_symm` as needed. |
| `HasSum.prod_fiberwise`, `Equiv.hasSum_iff` | Hilbert–Schmidt and Born probability sums | **Use directly**: reindex the product sum with `Equiv.prodComm` and identify each fiber via `HasSum.prod_fiberwise`; consumers keep the sum witness rather than reconstruct it from summability and a total equality. |
| Existing product-of-series primitives | `Analysis/InfiniteSum/FinsuppProduct` | **Retain** `Finsupp.hasSum_prod_nonneg`, `Finsupp.hasSum_prod`, and the geometric specialization: no theorem with their finite-`Finsupp` multisum statement was found in the pinned Mathlib product/sum APIs surveyed. |

For the newly introduced candidates, see
[Mathlib finite-product extension](https://github.com/leanprover-community/mathlib4/blob/v4.35.0/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean)
and [list interleaving](https://github.com/leanprover-community/mathlib4/blob/v4.35.0/Mathlib/Data/List/Interleave.lean).
These are **source-level assessments, not compiled replacement proofs**; do not remove
a declaration without checking its current uses and compiling affected consumers.

## Proof-guided Mathlib replacement discovery

`scripts/TheoremReplacementAudit.lean` checks more than the Mathlib theorems already used by each
project proof. It now builds a one-time index over imported Mathlib theorem conclusions and selects
candidate declarations with matching result heads, arity, and argument-head sketches. A relaxed
first-argument-head index admits related equations whose right-hand sides differ. Candidates
are ranked by argument-head agreement and binder-count distance; at most three *additional*
Mathlib candidates per project theorem are checked using Lean's direct-application engine.
Only the best few candidates are retained while traversing each fingerprint bucket, avoiding a full
sort of broad Mathlib conclusion classes.
Previously used Mathlib proof dependencies are checked separately without this discovery limit.

The generated `theorem-replacements.json` includes per-target
`mathlibDiscoveryShapeMatches` and `mathlibDiscoveryProbedCandidateCount`.
Verified matches continue to populate the existing `mathlibDefinitionallyEquivalentTo` and
`mathlibReplacementCandidates` fields, so downstream review tooling remains compatible.

**Limitations:** the syntactic index is intentionally incomplete, and the per-target cap makes
it a bounded candidate finder, not an exhaustive redundancy proof. Candidates still require
manual review of abstraction boundaries, downstream use, and total code reduction before removal.

## Remaining technical debt

`Analysis/InfiniteSum/FinsuppProduct.lean` contains finite-cardinality induction proofs.
The current implementation uses the default finite heartbeat budget, Mathlib's
`finSuccEquiv` and `Finsupp.optionEquiv` for reindexing, and the general product theorem
for the geometric specialization. Aggressively inlining the named summability witnesses
can exhaust Lean's heartbeat budget. Before upstreaming or broadening this API:

1. preserve tractable elaboration under the default finite heartbeat budget;
2. retain explicit summability witnesses where they prevent costly type inference;
3. minimize imports without losing required Mathlib declarations;
4. retain the geometric result as a corollary of the general product theorem.

## Current boundaries

The repository does not yet provide:

- trace-class approximation/completeness;
- a complete Schatten hierarchy;
- a Fredholm determinant on general trace-class operators;
- basis independence for unrelated diagonal presentations without spectral uniqueness;
- unbounded spectral/functional calculus with domains;
- a general completed-space interacting-Hamiltonian and Dyson theory beyond the existing
  fermionic diagonal/CAR and bosonic weighted-ladder/quartic partial-map constructions.

These are future analysis targets rather than gaps to be hidden by compatibility wrappers.

## Weak algebraic derivatives and operator restrictions

- `HasAlgebraicDerivAt` and its rules require a nontrivially normed scalar field, not a complex-specific structure. The target remains purely algebraic: scalar testing uses all algebraic linear functionals, not only continuous ones. Ordinary Mathlib derivative rules supply the scalar calculus.
- `NormedSpace.exp_apply_of_eigenvector` retains the direct series bridge between the bounded operator and its scalar eigenvalue. The power step uses the standard opposite orientations of `pow_succ` and `pow_succ'`, without ring normalization. Mathlib's `map_exp` needs a continuous ring homomorphism; evaluation on a vector is not such a homomorphism.
- Retain `Subalgebra.restrictEnd`: the pinned Mathlib `LinearMap.restrict` handles individual maps and its source explicitly notes the missing bundled algebra-homomorphism version. The Holstein–Primakoff consumer needs multiplicative and unital restriction.

## Matrix characteristic polynomials and interval support

- `Analysis/Matrix/FinTwoCharpoly` already uses Mathlib's `Matrix.charpoly_fin_two` and `Matrix.aeval_self_charpoly` for the crystallographic finite-order identities. Keep the specialized conclusions used by the crystal classification; the fourth-power step can use a squared negative identity directly.
- `Analysis/Calculus/CompactSupportInterval` uses `Function.support_mul_subset_left` and `tsupport_deriv_subset` rather than reconstructing pointwise support arguments. The oriented full-line indicator construction and its integral laws are no longer complex-specific. Equality of total integrals does not itself imply integrability.

## Finite Fourier character orthogonality

Mathlib's `AddChar.wInner_cWeight_eq_boole` already proves orthogonality of complex characters of arbitrary finite abelian groups for the average inner product. `AddChar.orthonormal_normalized_family` converts this to the counting-measure `EuclideanSpace` normalization for any injective indexing family; the cyclic Fourier modes specialize it via `stdAddChar.mulShift`. Downstream use `AddChar.map_neg_eq_conj` and the orthonormality of the Fourier basis directly. The positive-exponent convention is unchanged.
