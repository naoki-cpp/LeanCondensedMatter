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

**Still needed to close step 1:** (a) the index type is not yet shown to be countable (needs a compactness argument: only finitely many eigenvalues can exceed any `ε > 0` in absolute value, else orthonormal eigenvectors with eigenvalue bounded away from `0` would have no convergent-image subsequence, contradicting compactness of `T`); (b) the `tsum` reconstruction `T x = ∑' i, (eigenvalue i : ℂ) • ⟪eigenvectorFamily i, x⟫ • eigenvectorFamily i` is not proved (needs `T`'s continuity plus density of the eigenspace sum, from `orthogonalComplement_iSup_eigenspaces_eq_bot`).
