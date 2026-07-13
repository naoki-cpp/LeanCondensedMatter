# Roadmap — Operator algebra (Track C)

See [notes/roadmap.md](../roadmap.md) for the status table and how this track fits into the overall plan.

Track C covers infinite-dimensional operator-algebraic foundations needed once Track A moves beyond finite-dimensional Hilbert spaces. The immediate, concrete target is trace-class operator theory (below); the track name is kept broad because further operator-algebraic infrastructure (e.g. C*-algebra structure on bounded operators, needed if functional-calculus-style constructions come up again) may be added here as later targets, rather than opening a new track each time.

## Trace-class / Hilbert-Schmidt operator theory

Status: `stated`.

**Motivation.** `QuantumTheory.DensityOperator`, `QuantumTheory.vonNeumannEntropy`, and `QuantumTheory.gibbsState` (`LeanCondensedMatter/QuantumTheory/`) are currently scoped to finite-dimensional Hilbert spaces, because they are built on `LinearMap.trace`, which requires `[FiniteDimensional 𝕜 E]`. The Linked Cluster Theorem target needs a countably-infinite-dimensional Hilbert space (Fock space over a lattice), so a notion of trace that works in infinite dimensions is a prerequisite for extending Track A beyond finite dimensions. See `notes/caveats.md` for the original statement of this gap.

**Mathlib survey (2026, at the pinned revision):** confirmed no existing infrastructure. Searched for `Schatten`, `TraceClass`, `HilbertSchmidt`, `nuclear operator` across all of Mathlib: zero hits. What exists nearby, and what each one is missing for this purpose:
- `Mathlib/Analysis/Normed/Operator/Compact/Basic.lean` — `IsCompactOperator`, general normed-space compact operators; no inner-product-space/self-adjoint spectral theory attached.
- `Mathlib/Analysis/InnerProductSpace/Spectrum.lean` — spectral theorem for self-adjoint operators, but the finite-dimensional part (`eigenvalues`, `eigenvectorBasis`) is what this project already uses; the file's infinite-dimensional part covers only general orthogonality/eigenspace facts, not a full countable diagonalization.
- `Mathlib/Analysis/InnerProductSpace/Trace.lean` — `LinearMap.trace_eq_sum_inner`, `IsSymmetric.trace_eq_sum_eigenvalues`; explicitly requires `[Fintype ι]`/`[FiniteDimensional 𝕜 E]`.
- `Mathlib/Analysis/InnerProductSpace/SingularValues.lean` — `LinearMap.singularValues`; docstring explicitly states it is for finite-dimensional linear maps (finitely-supported singular value sequence).

No TODO comments or Zulip-referenced plans found suggesting this is in progress upstream — this looks like a genuine, currently-unclaimed gap rather than duplicated effort. No known external Lean 4 library (checked: not vendored anywhere in this repo; not aware of one from general knowledge, unverified).

**Rough scope** (minimal path to "trace of a self-adjoint compact operator via its eigenvalue sequence"):
1. Extend the compact self-adjoint spectral theorem from finite dimensions (`InnerProductSpace/Spectrum.lean`) to a countable orthonormal eigenbasis with eigenvalues forming a sequence tending to `0`. **Done** — see below (the "sequence tending to `0`" part follows from `finite_large_eigenvalue_index` but is not separately packaged as a `Tendsto` statement; `hasSum_eigenvectorFamily`'s `HasSum` already implies the terms tend to `0`, which is what's actually needed downstream).
2. Define an `IsTraceClass` predicate (e.g. `Summable` of the eigenvalue/singular-value sequence), and prove it is independent of the choice of eigenbasis. **Done** — see below.
3. Optional easier stepping stone first: Hilbert-Schmidt operators, via `Summable (fun i => ‖T (e i)‖^2)` for an orthonormal basis `e` — simpler than trace-class since it needs no ordering/positivity, only `ℓ²` membership. **Superseded** — step 1 solved the harder eigenvector-decomposition problem directly, so this easier stepping stone is no longer needed as a prerequisite; left undone as its own target unless a future use case wants Hilbert-Schmidt operators specifically (e.g. for a Hilbert-Schmidt inner product space structure).
4. Define trace on trace-class operators via the summable eigenvalue sum, and prove linearity/cyclicity lemmas mirroring the finite-dimensional ones already used in `LeanCondensedMatter/QuantumTheory/Entropy.lean`. **Done** — see below (`trace`, `trace_nonneg`, `trace_smul`, `trace_add`, `trace_comp_comm` all proved).

This is scoped as its own track (not folded into Track A) because it is foundational analysis work, independent of the physics content, and is likely a substantial undertaking in its own right — comparable in size to Track B's combinatorics work.

### Progress on step 1: a countable orthonormal family of eigenvectors

`ContinuousLinearMap.orthonormal_eigenvectorFamily` (`LeanCondensedMatter/Analysis/CompactSelfAdjoint.lean`) — for a compact self-adjoint `T`, glues an orthonormal basis of each nonzero eigenspace (obtained via `stdOrthonormalBasis`, finite-dimensional by `finite_dimensional_eigenspace`) into one orthonormal family `ContinuousLinearMap.eigenvectorFamily`, indexed by `Σ μ : {μ : ℝ // μ ≠ 0}, Fin (finrank ℂ (eigenspace T μ))`, using `OrthogonalFamily.orthonormal_sigma_orthonormal` combined with `LinearMap.IsSymmetric.orthogonalFamily_eigenspaces` (restricted from `ℂ`-indexed to `ℝ`-indexed via `OrthogonalFamily.comp` and injectivity of the real-to-complex embedding). The `μ = 0` eigenspace (the kernel of `T`, possibly infinite-dimensional or non-separable) is deliberately excluded, since it contributes nothing to the trace.

`ContinuousLinearMap.apply_eigenvectorFamily` — each vector of `eigenvectorFamily` really is an eigenvector of `T`, with the eigenvalue recorded in its index (from membership in the eigenspace submodule).

`ContinuousLinearMap.finite_large_eigenvalue_index` — for `ε > 0`, only finitely many indices have eigenvalue `≥ ε` in absolute value. Proved by contradiction: infinitely many such indices would give an orthonormal sequence `(eₙ)` (via `Set.Infinite.natEmbedding`) whose images `T eₙ` stay pairwise at distance `≥ ε√2` (Pythagoras, using orthogonality of eigenvectors for distinct eigenvalues), while compactness of `T` (`IsCompactOperator.image_closedBall_subset_compact` + `IsCompact.tendsto_subseq`) forces a norm-convergent, hence Cauchy, subsequence of `T ∘ e` — contradiction.

`ContinuousLinearMap.countable_eigenvectorIndex` — **`EigenvectorIndex T` is countable.** `Set.univ` is the union, over `n : ℕ`, of the finite sets of indices with eigenvalue `≥ 1/(n+1)` in absolute value (every nonzero eigenvalue exceeds some such threshold, by the Archimedean property `exists_nat_one_div_lt`); a countable union of finite sets is countable. This closes step 1's countability requirement.

`ContinuousLinearMap.span_eigenvectorFamily` — the (algebraic) span of `eigenvectorFamily` equals exactly `⨆ μ ≠ 0, eigenspace T μ`: each per-eigenspace `stdOrthonormalBasis` spans its own eigenspace (`Basis.span_eq`, pushed forward along the submodule inclusion via `Submodule.map_span`/`Submodule.map_top`/`Submodule.range_subtype`), and these combine the same way the index type does.

`ContinuousLinearMap.orthogonal_closure_span_eigenvectorFamily` — **the closure of `eigenvectorFamily`'s span and `ker T` are exactly each other's orthogonal complements.** Proved via the general Hilbert-space fact "two closed mutually-orthogonal subspaces whose sum is dense are each other's orthogonal complements" (`v ∈ Fᗮ` decomposes as `g + g'` with `g ∈ ker T ⊆ Fᗮ`, `g' ∈ (ker T)ᗮ`; then `g' ∈ Fᗮ ⊓ (ker T)ᗮ = (F ⊔ ker T)ᗮ = ⊥` since `F ⊔ ker T` is dense, forcing `g' = 0`). Density of `ker T ⊔ eigenvectorFamily`'s span comes from `orthogonalComplement_iSup_eigenspaces_eq_bot` applied to the sum over *all* complex eigenvalues, combined with the fact that a self-adjoint operator's eigenvalues are always real (`LinearMap.IsSymmetric.conj_eigenvalue_eq_self`), so no eigenspace outside `ℝ` contributes to that sum.

`ContinuousLinearMap.eigenvectorHilbertBasis` — `eigenvectorFamily`, recast as a genuine `HilbertBasis (EigenvectorIndex T) ℂ F` of the closed subspace `F` it spans. Built via `HilbertBasis.mkOfOrthogonalEqBot`, using that the family's span is dense *within* `F` (an `IsInducing.dense_iff` argument on the subtype embedding `F.subtypeₗᵢ`, reducing density in `F` to the known fact `F = E'.topologicalClosure` in `H`) for the orthogonal-complement-in-`F` hypothesis, and that orthogonality/norms transfer along the isometric submodule inclusion for the orthonormality hypothesis.

`ContinuousLinearMap.hasSum_eigenvectorFamily` — **the `tsum` reconstruction itself, closing step 1 in full:** for any `x : H`,
`HasSum (fun a => (eigenvalue a : ℂ) • ⟪eigenvectorFamily a, x⟫ • eigenvectorFamily a) (T x)`.
Proved by taking `HilbertBasis.hasSum_orthogonalProjectionOnto` for `eigenvectorHilbertBasis` (giving the `F`-component of `x` as a `HasSum` in `F`), pushing it out to `H` and then through `T` via `HasSum.mapL` (twice), and simplifying: `T` sends the `F`-projection of `x` to `T x` itself (since `x` minus its `F`-projection lies in `Fᗮ = ker T`, by `orthogonal_closure_span_eigenvectorFamily`, which `T` kills), and `T` sends each eigenvector term to itself scaled by its eigenvalue (`apply_eigenvectorFamily`).

### Progress on step 2: the `IsTraceClass` predicate

`ContinuousLinearMap.IsTraceClass` — `T` is trace-class when `Summable (fun a : EigenvectorIndex T => |a.1.1|)` (the absolute values of `T`'s nonzero eigenvalues, with multiplicity, are summable). No separate "independent of the choice of eigenbasis" lemma was needed: `EigenvectorIndex T` and the eigenvalue at each index depend only on `T`'s eigenspaces and their dimensions, not on which orthonormal basis was chosen within each (possibly multi-dimensional) eigenspace — every basis vector of a given eigenspace shares the same eigenvalue, so the predicate is manifestly insensitive to that choice by construction (documented in the declaration's docstring rather than proved as a separate lemma, since there is nothing left to prove).

### Progress on step 4: the `trace` definition

`ContinuousLinearMap.trace` — `trace h := ∑' a : EigenvectorIndex T, a.1.1` for `h : IsTraceClass T` — the trace of a trace-class compact self-adjoint operator, defined as the sum of its (nonzero) eigenvalues with multiplicity. The infinite-dimensional analogue of `LinearMap.trace` used throughout `QuantumTheory/Entropy.lean`.

`ContinuousLinearMap.trace_nonneg` — the trace of a positive trace-class operator is nonnegative, mirroring the finite-dimensional fact used for density operators (`QuantumTheory.DensityOperator`) that every eigenvalue of a positive operator is nonnegative (via Mathlib's own `eigenvalue_nonneg_of_nonneg`).

`ContinuousLinearMap.trace_smul` — `trace (c • T) = c * trace T` for `c ≠ 0`, scalar-multiplication linearity. Proved by splitting each trace-defining `tsum` into an outer `tsum` over the (non-dependent) base eigenvalue type and an inner *finite* sum over each eigenspace's basis vectors (`tsum_eigenvectorIndex_eq_tsum_mul_finrank`), rather than by building a reindexing `Equiv (EigenvectorIndex T) (EigenvectorIndex (c • T))` between the two dependent `Sigma` types directly — several attempts at the latter hit genuine kernel timeouts, not just slow builds; see `notes/caveats.md` for the full account and the reusable lesson (split the sum, don't reindex the dependent type, whenever the summand doesn't depend on the fiber index).

`ContinuousLinearMap.HilbertBasis.hasSum_norm_sq_inner` — Parseval's identity for a `HilbertBasis`, in norm-squared form: `HasSum (fun i => ‖⟪x, d i⟫‖ ^ 2) (‖x‖ ^ 2)`. A small reusable fact, proved via `⟪x,dᵢ⟩*⟪dᵢ,x⟩` always being exactly the real cast of its own squared magnitude (`Complex.mul_conj`/`inner_conj_symm`), combined with `HilbertBasis.hasSum_inner_mul_inner`.

`ContinuousLinearMap.tsum_norm_sq_orthogonalProjectionOnto_eq_finrank` — the trace of a finite-rank orthogonal projection, computed against *any* Hilbert basis of the ambient space, equals its rank. Not used directly by `trace_add` in the end (see below), but a standalone reusable fact about basis-independence of finite-rank-projection traces.

`ContinuousLinearMap.hasSum_inner_apply_eq_trace` — **`trace` can be computed against any Hilbert basis of `H`, not just the eigenbasis used in its definition**: `HasSum (fun i => ⟪dᵢ, T dᵢ⟩.re) (trace h)` for *any* `HilbertBasis ι ℂ H`. This is the basis-independence fact that makes additive linearity provable at all. Proved by applying Parseval directly to each (already unit-norm) eigenvector individually — no need to group by eigenspace — then justifying the order-of-summation swap (`Σᵢ Σₐ ↔ Σₐ Σᵢ`, both over genuinely infinite index sets) via `summable_prod_of_nonneg` (bounding the absolute-value double family by the trace-class hypothesis) and `HasSum.prod_fiberwise` (rather than the weaker `Summable.tsum_comm'`, since a *genuine* `HasSum` — not just a `tsum` equality — is needed to combine two operators' traces additively via `HasSum.add`).

`ContinuousLinearMap.trace_add` — **additive linearity of `trace`**, `trace (T + T') = trace T + trace T'`, for trace-class compact self-adjoint `T`, `T'` whose sum is also trace-class (compactness/self-adjointness of the sum are taken as explicit hypotheses rather than derived). Proved by comparing all three operators against a *common* Hilbert basis of `H` (via `hasSum_inner_apply_eq_trace` and `exists_hilbertBasis`), sidestepping the fact that `T`'s and `T'`'s own eigenbases are generally unrelated.

`ContinuousLinearMap.trace_comp_comm` — **cyclicity of `trace`**, `trace (T * T') = trace (T' * T)`, for self-adjoint compact `T`, `T'` whose compositions (both orders) are compact self-adjoint trace-class. Turned out to be *simpler* than `trace_add`, not harder as originally anticipated: against a common Hilbert basis `d`, self-adjointness gives `⟪dᵢ, T (T' dᵢ)⟫ = ⟪T dᵢ, T' dᵢ⟫` and `⟪dᵢ, T' (T dᵢ)⟫ = ⟪T' dᵢ, T dᵢ⟫` directly (`IsSymmetric`'s defining equation, no rewriting needed beyond that), and `⟪T' dᵢ, T dᵢ⟫` is exactly the complex conjugate of `⟪T dᵢ, T' dᵢ⟫` (`inner_conj_symm`) — so the two summands' real parts are equal *term by term*, with no order-of-summation swap (`HasSum.prod_fiberwise`/`summable_prod_of_nonneg`) needed at all, unlike `trace_add`.

Step 4 is now closed: `trace`, `trace_nonneg`, `trace_smul`, `trace_add`, and `trace_comp_comm` are all proved.

## Hilbert–Schmidt operators

Status: `stated`.

**Motivation.** `ContinuousLinearMap.trace` only applies to compact self-adjoint trace-class operators. The Born-rule probability `Tr[E_m ρ]` needs a trace-like quantity for `E_m ∘ ρ`, which need not be self-adjoint even when `E_m`, `ρ` both are. The standard fix: if `S`, `T` are Hilbert–Schmidt, `S† ∘ T` is trace-class regardless of self-adjointness, with `Tr[S† ∘ T] = Σᵢ ⟪S dᵢ, T dᵢ⟫` well-defined via the Hilbert–Schmidt inner product — no self-adjointness needed anywhere in this construction. See `LeanCondensedMatter/Analysis/HilbertSchmidt.lean`.

**Rough scope:** (1) the Hilbert–Schmidt predicate and its basis-independence — **done**, see below; (2) closure under composition with a bounded operator (`bounded ∘ HS = HS`, `HS ∘ bounded = HS`); (3) the Hilbert–Schmidt inner product `⟪S,T⟫_HS := Σᵢ⟪S dᵢ,T dᵢ⟫` and its convergence/basis-independence; (4) connecting `S† ∘ T`'s `⟪·,·⟫_HS`-derived trace back to `ContinuousLinearMap.trace` when `S = T` is also self-adjoint compact trace-class (consistency check); (5) applying this to the Born rule (`QuantumTheory.TraceClass.POVM`/`prob`/`sum_prob_eq_one`).

### Progress on step 1: the Hilbert–Schmidt predicate and its basis-independence

`ContinuousLinearMap.IsHilbertSchmidtWrt d T` — `T` is Hilbert–Schmidt with respect to a given Hilbert basis `d`: `Summable (fun i => ‖T (d i)‖ ^ 2)`. Defined for *any* bounded `T` — no self-adjointness required.

`ContinuousLinearMap.summable_norm_sq_adjoint_apply_and_tsum_eq` — **the core basis-independence computation**: if `T` is Hilbert–Schmidt with respect to a basis `d`, its adjoint `T†` is Hilbert–Schmidt with respect to *any* basis `f`, with the same sum of squared norms (`Σᵢ‖T dᵢ‖² = Σⱼ‖T† fⱼ‖²`). Proved via the same order-of-summation-swap technique used for `ContinuousLinearMap.hasSum_inner_apply_eq_trace` (Track C step 4) — `summable_prod_of_nonneg` plus a `Summable.tsum_prod'`/`Equiv.prodComm` chain — but genuinely *simpler* here since every summand is already nonnegative (`‖·‖²`), avoiding the sign-tracking (`Summable.of_abs`, `HasSum.prod_fiberwise`) needed in the trace-class case.

`ContinuousLinearMap.isHilbertSchmidtWrt_iff` / `IsHilbertSchmidt` / `isHilbertSchmidt_iff_isHilbertSchmidtWrt` — applying the core computation twice (once for `T`, once for `T†`, using `T†† = T`) gives genuine basis-independence: `IsHilbertSchmidtWrt d T ↔ IsHilbertSchmidtWrt f T` for *any* two bases `d`, `f`. `IsHilbertSchmidt T` packages this as `∃ (w : Set H) (d : HilbertBasis w ℂ H), IsHilbertSchmidtWrt d T` — using `Set H` (as `exists_hilbertBasis` does), not an arbitrary `Type*`, to avoid a universe-polymorphism mismatch when destructuring the existential against an already-fixed basis at a different universe.

### Progress on step 2: composition closure

`ContinuousLinearMap.isHilbertSchmidt_adjoint` — Hilbert–Schmidt-ness is preserved by taking the adjoint: if `T` is Hilbert–Schmidt with respect to a basis `d`, then `T†` is Hilbert–Schmidt with respect to that *same* `d`, directly from `summable_norm_sq_adjoint_apply_and_tsum_eq d d T`.

`ContinuousLinearMap.isHilbertSchmidtWrt_comp_left` / `isHilbertSchmidt_comp_left` — **`B * T` is Hilbert–Schmidt whenever `T` is, for any bounded `B`** (with respect to the same basis as `T`). Proved by the comparison test: `‖B (T dᵢ)‖ ≤ ‖B‖ * ‖T dᵢ‖` (`ContinuousLinearMap.le_opNorm`), so `‖(B*T) dᵢ‖² ≤ ‖B‖² * ‖T dᵢ‖²`, and `Summable.of_nonneg_of_le` against `‖B‖² • (‖T dᵢ‖²)`'s summability closes it.

`ContinuousLinearMap.isHilbertSchmidt_comp_right` — **`T * B` is Hilbert–Schmidt whenever `T` is, for any bounded `B`.** Reduced to the left-composition case via the adjoint identity `(T * B)† = B† * T†` (proved by unfolding `†` to `star` via `ContinuousLinearMap.star_eq_adjoint` and using `star_mul`/`star_star` from the ambient star-ring structure on `H →L[ℂ] H`, since Mathlib has no direct `adjoint_mul` lemma for `*`, only `adjoint_comp` for `∘L`): `T†` is Hilbert–Schmidt (`isHilbertSchmidt_adjoint`), so `B† * T†` is Hilbert–Schmidt (`isHilbertSchmidt_comp_left`), so its adjoint `T * B` is Hilbert–Schmidt (`isHilbertSchmidt_adjoint` again, using `T†† = T`).

Step 2 is now closed: Hilbert–Schmidt operators are closed under composition with any bounded operator on either side.

### Progress on step 3: the Hilbert–Schmidt inner product

`ContinuousLinearMap.innerHS d S T` — `Σᵢ ⟪S dᵢ, T dᵢ⟫`, the Hilbert–Schmidt inner product of `S`, `T` with respect to a basis `d` (`noncomputable`, since it unfolds to a `tsum`).

`ContinuousLinearMap.summable_inner_apply_of_isHilbertSchmidtWrt` — convergence: for `S`, `T` Hilbert–Schmidt with respect to `d`, `Σᵢ ⟪S dᵢ, T dᵢ⟫` is summable, via the AM–GM bound `|⟪S dᵢ, T dᵢ⟫| ≤ ‖S dᵢ‖‖T dᵢ‖ ≤ (‖S dᵢ‖² + ‖T dᵢ‖²)/2` and comparison against the (summable, by hypothesis) sum of squared norms.

`ContinuousLinearMap.hasSum_inner_swap` — **the core Fubini computation.** For `S`, `T` Hilbert–Schmidt with respect to `d`, and *any* other basis `f`: the double family `g(i,j) := ⟪S dᵢ, fⱼ⟫ ⟪fⱼ, T dᵢ⟫` sums row-first (via the resolution of the identity along `f`, `HilbertBasis.hasSum_inner_mul_inner`) to `Σᵢ ⟪S dᵢ, T dᵢ⟫`, and column-first (via the resolution of the identity along `d`, after rewriting each factor through the adjoint with `adjoint_inner_left`/`adjoint_inner_right`) to `Σⱼ ⟪T† fⱼ, S† fⱼ⟫`. Unlike the analogous squared-norm swap for `IsHilbertSchmidtWrt`, the summands here are complex (not nonnegative), so absolute summability of the double family is established via the same AM–GM bound rather than `summable_prod_of_nonneg` applied directly to the family; the two iterated sums are then equated against a common total via `HasSum.prod_fiberwise` (applied once to the family and once to its swap), which — unlike `summable_prod_of_nonneg` — needs no sign hypothesis.

`ContinuousLinearMap.innerHS_eq_of_isHilbertSchmidt` — **`innerHS` is independent of the choice of basis.** Applying `hasSum_inner_swap` with `f := d` (the *same* basis in both argument slots) identifies `innerHS d S T` with `Σᵢ ⟪T† dᵢ, S† dᵢ⟫`; applying it again with `d` and `f` swapped identifies that same quantity `Σᵢ ⟪T† dᵢ, S† dᵢ⟫` with `innerHS f S T`. Chaining the two equalities closes the loop — the same two-application trick used for `isHilbertSchmidtWrt_iff` (Track C step 1), but here both applications share the *second* basis argument (`d`) rather than exploiting `T†† = T`.

Step 3 is now closed: the Hilbert–Schmidt inner product is well-defined, independent of the choice of basis.

### Progress on step 4: reconciliation with `ContinuousLinearMap.trace`

`ContinuousLinearMap.innerHS_one_eq_trace` — for a compact self-adjoint trace-class `A`, `innerHS d 1 A = (trace hAtc : ℂ)` (the Hilbert–Schmidt inner product of the identity against `A`, cast to `ℂ`, equals the eigenvalue-sum `trace` already defined for the self-adjoint case). Proved by: (1) `⟪1 dᵢ, A dᵢ⟫ = ⟪dᵢ, A dᵢ⟫` (`one_apply_eq_self`); (2) each `⟪dᵢ, A dᵢ⟫` is real, since self-adjointness (`A.IsSymmetric`) plus `inner_conj_symm` gives `conj ⟪dᵢ, A dᵢ⟫ = ⟪dᵢ, A dᵢ⟫`, hence `⟪dᵢ, A dᵢ⟫ = ((⟪dᵢ,A dᵢ⟫).re : ℂ)` (`Complex.conj_eq_iff_re`); (3) pushing `hasSum_inner_apply_eq_trace`'s `HasSum` of the real parts through the continuous embedding `Complex.ofRealCLM` (`HasSum.mapL`) and combining with (1)–(2) identifies the two sums termwise, so their `tsum`s agree.

This is a minimal-but-representative reconciliation: it identifies the two notions of trace on the overlap of their domains (self-adjoint operators via `S := 1`) rather than proving the fully general statement `innerHS d S T = trace (S† ∘ T)` for arbitrary Hilbert–Schmidt `S`, `T` — the latter would need `ContinuousLinearMap.trace` extended to (not-necessarily-self-adjoint) trace-class operators first, which is out of scope here. Step 4 is closed for this purpose.

**Still needed:** step 5 above (applying this to the Born rule) is now done directly in `QuantumTheory.TraceClass` — see `notes/roadmaps/quantum-theory-foundations.md` — via `ρ`'s own eigendecomposition, sidestepping the Hilbert–Schmidt inner product entirely (see the note there for why). The Hilbert–Schmidt track itself (steps 1–4) is complete; no further steps are currently planned here.

## Continuous functional calculus acts on eigenvectors by evaluation

Status: `proved`.

`cfc_apply_eigenvector` — `cfc f T v = (f c : ℂ) • v` for a self-adjoint `T`, continuous `f : ℝ → ℝ`, and eigenvector `v` with `T v = (c:ℂ) • v` — a general-purpose bridge between Mathlib's continuous functional calculus (`cfc`, usable on `H →L[ℂ] H` via its `CStarAlgebra` instance) and explicit eigenbasis constructions. `cfc` is the natural infinite-dimensional replacement for the eigenbasis-sum constructions used throughout `LeanCondensedMatter/QuantumTheory/Entropy.lean` (finite dimensions can enumerate eigenvalues; infinite dimensions generally cannot), so this lemma is a prerequisite piece of Track C groundwork, developed in `LeanCondensedMatter/Analysis/CFC.lean`.

`Polynomial.aeval_apply_eigenvector` — the polynomial-functional-calculus case, `(Polynomial.aeval T q) v = (q.eval c : ℂ) • v` for `q : ℝ[X]`, by induction on `q`.

`cfc_apply_eigenvector` extends this to general continuous `f` by approximating `f` uniformly by polynomials `pₙ` on `[-‖T‖, ‖T‖]` (a compact interval containing `spectrum ℝ T`, via the classical Weierstrass approximation theorem `exists_polynomial_near_of_continuousOn` — this sidesteps needing `c ∈ spectrum ℝ T` explicitly, since the bound holds on all of `[-‖T‖,‖T‖]`), then passing to the limit: `cfc pₙ.eval T → cfc f T` in operator norm (via `IsGreatest.norm_cfc`, which identifies `‖cfc g T‖` with the sup of `|g|` over `spectrum ℝ T`) while `cfc pₙ.eval T v = (pₙ.eval c : ℂ) • v → (f c : ℂ) • v` (via `Polynomial.aeval_apply_eigenvector` plus continuity of evaluation at `c`), and uniqueness of limits closes the gap. See `notes/caveats.md` for a Mathlib pitfall hit along the way (`IsStarNormal.instContinuousFunctionalCalculus` is only a `local instance`).
