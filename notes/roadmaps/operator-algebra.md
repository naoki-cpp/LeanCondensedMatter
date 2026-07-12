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
1. Extend the compact self-adjoint spectral theorem from finite dimensions (`InnerProductSpace/Spectrum.lean`) to a countable orthonormal eigenbasis with eigenvalues forming a sequence tending to `0`. **Partially done** — see below.
2. Define an `IsTraceClass` predicate (e.g. `Summable` of the eigenvalue/singular-value sequence), and prove it is independent of the choice of eigenbasis.
3. Optional easier stepping stone first: Hilbert-Schmidt operators, via `Summable (fun i => ‖T (e i)‖^2)` for an orthonormal basis `e` — simpler than trace-class since it needs no ordering/positivity, only `ℓ²` membership.
4. Define trace on trace-class operators via the summable eigenvalue sum, and prove linearity/cyclicity lemmas mirroring the finite-dimensional ones already used in `LeanCondensedMatter/QuantumTheory/Entropy.lean`.

This is scoped as its own track (not folded into Track A) because it is foundational analysis work, independent of the physics content, and is likely a substantial undertaking in its own right — comparable in size to Track B's combinatorics work.

### Progress on step 1: a countable orthonormal family of eigenvectors

`ContinuousLinearMap.orthonormal_eigenvectorFamily` (`LeanCondensedMatter/Analysis/CompactSelfAdjoint.lean`) — for a compact self-adjoint `T`, glues an orthonormal basis of each nonzero eigenspace (obtained via `stdOrthonormalBasis`, finite-dimensional by `finite_dimensional_eigenspace`) into one orthonormal family `ContinuousLinearMap.eigenvectorFamily`, indexed by `Σ μ : {μ : ℝ // μ ≠ 0}, Fin (finrank ℂ (eigenspace T μ))`, using `OrthogonalFamily.orthonormal_sigma_orthonormal` combined with `LinearMap.IsSymmetric.orthogonalFamily_eigenspaces` (restricted from `ℂ`-indexed to `ℝ`-indexed via `OrthogonalFamily.comp` and injectivity of the real-to-complex embedding). The `μ = 0` eigenspace (the kernel of `T`, possibly infinite-dimensional or non-separable) is deliberately excluded, since it contributes nothing to the trace.

`ContinuousLinearMap.apply_eigenvectorFamily` — each vector of `eigenvectorFamily` really is an eigenvector of `T`, with the eigenvalue recorded in its index (from membership in the eigenspace submodule).

`ContinuousLinearMap.finite_large_eigenvalue_index` — for `ε > 0`, only finitely many indices have eigenvalue `≥ ε` in absolute value. Proved by contradiction: infinitely many such indices would give an orthonormal sequence `(eₙ)` (via `Set.Infinite.natEmbedding`) whose images `T eₙ` stay pairwise at distance `≥ ε√2` (Pythagoras, using orthogonality of eigenvectors for distinct eigenvalues), while compactness of `T` (`IsCompactOperator.image_closedBall_subset_compact` + `IsCompact.tendsto_subseq`) forces a norm-convergent, hence Cauchy, subsequence of `T ∘ e` — contradiction.

`ContinuousLinearMap.countable_eigenvectorIndex` — **`EigenvectorIndex T` is countable.** `Set.univ` is the union, over `n : ℕ`, of the finite sets of indices with eigenvalue `≥ 1/(n+1)` in absolute value (every nonzero eigenvalue exceeds some such threshold, by the Archimedean property `exists_nat_one_div_lt`); a countable union of finite sets is countable. This closes step 1's countability requirement.

`ContinuousLinearMap.span_eigenvectorFamily` — the (algebraic) span of `eigenvectorFamily` equals exactly `⨆ μ ≠ 0, eigenspace T μ`: each per-eigenspace `stdOrthonormalBasis` spans its own eigenspace (`Basis.span_eq`, pushed forward along the submodule inclusion via `Submodule.map_span`/`Submodule.map_top`/`Submodule.range_subtype`), and these combine the same way the index type does.

`ContinuousLinearMap.orthogonal_closure_span_eigenvectorFamily` — **the closure of `eigenvectorFamily`'s span and `ker T` are exactly each other's orthogonal complements.** Proved via the general Hilbert-space fact "two closed mutually-orthogonal subspaces whose sum is dense are each other's orthogonal complements" (`v ∈ Fᗮ` decomposes as `g + g'` with `g ∈ ker T ⊆ Fᗮ`, `g' ∈ (ker T)ᗮ`; then `g' ∈ Fᗮ ⊓ (ker T)ᗮ = (F ⊔ ker T)ᗮ = ⊥` since `F ⊔ ker T` is dense, forcing `g' = 0`). Density of `ker T ⊔ eigenvectorFamily`'s span comes from `orthogonalComplement_iSup_eigenspaces_eq_bot` applied to the sum over *all* complex eigenvalues, combined with the fact that a self-adjoint operator's eigenvalues are always real (`LinearMap.IsSymmetric.conj_eigenvalue_eq_self`), so no eigenspace outside `ℝ` contributes to that sum.

**Still needed to close step 1:** the `tsum` reconstruction `T x = ∑' i, (eigenvalue i : ℂ) • ⟪eigenvectorFamily i, x⟫ • eigenvectorFamily i` itself — the structural fact above is now in place, but still needs (a) a `HilbertBasis`-style reconstruction of the closed subspace `F`'s component of `x` in terms of `eigenvectorFamily`, and (b) pushing `T` through the resulting `HasSum` via `ContinuousLinearMap.hasSum`/`HasSum.mapL`, using that `T` kills the `ker T` component.

## Continuous functional calculus acts on eigenvectors by evaluation

Status: `proved`.

`cfc_apply_eigenvector` — `cfc f T v = (f c : ℂ) • v` for a self-adjoint `T`, continuous `f : ℝ → ℝ`, and eigenvector `v` with `T v = (c:ℂ) • v` — a general-purpose bridge between Mathlib's continuous functional calculus (`cfc`, usable on `H →L[ℂ] H` via its `CStarAlgebra` instance) and explicit eigenbasis constructions. `cfc` is the natural infinite-dimensional replacement for the eigenbasis-sum constructions used throughout `LeanCondensedMatter/QuantumTheory/Entropy.lean` (finite dimensions can enumerate eigenvalues; infinite dimensions generally cannot), so this lemma is a prerequisite piece of Track C groundwork, developed in `LeanCondensedMatter/Analysis/CFC.lean`.

`Polynomial.aeval_apply_eigenvector` — the polynomial-functional-calculus case, `(Polynomial.aeval T q) v = (q.eval c : ℂ) • v` for `q : ℝ[X]`, by induction on `q`.

`cfc_apply_eigenvector` extends this to general continuous `f` by approximating `f` uniformly by polynomials `pₙ` on `[-‖T‖, ‖T‖]` (a compact interval containing `spectrum ℝ T`, via the classical Weierstrass approximation theorem `exists_polynomial_near_of_continuousOn` — this sidesteps needing `c ∈ spectrum ℝ T` explicitly, since the bound holds on all of `[-‖T‖,‖T‖]`), then passing to the limit: `cfc pₙ.eval T → cfc f T` in operator norm (via `IsGreatest.norm_cfc`, which identifies `‖cfc g T‖` with the sup of `|g|` over `spectrum ℝ T`) while `cfc pₙ.eval T v = (pₙ.eval c : ℂ) • v → (f c : ℂ) • v` (via `Polynomial.aeval_apply_eigenvector` plus continuity of evaluation at `c`), and uniqueness of limits closes the gap. See `notes/caveats.md` for a Mathlib pitfall hit along the way (`IsStarNormal.instContinuousFunctionalCalculus` is only a `local instance`).
