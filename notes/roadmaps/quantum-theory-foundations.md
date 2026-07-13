# Roadmap — Quantum theory foundations (Track A)

See [notes/roadmap.md](../roadmap.md) for the status table and how this track fits into the overall plan.

## Minimal axiomatic quantum theory foundation

Status: `stated`.

State-space postulate and observable definition (`QuantumTheory.State`, `QuantumTheory.Observable`) and the expectation value they define, with reality of expectation values proved (`expValue_im_eq_zero`) and phase indeterminacy proved (`expValue_smul_of_norm_eq_one`). See `LeanCondensedMatter/QuantumTheory/Postulates.lean` and `notes/model-and-assumptions.md`. Entry point beneath the QFT groundwork target below.

## Density operators and the Born rule (finite-dimensional)

Status: `stated`.

Density-operator postulate (`QuantumTheory.DensityOperator`, positive trace-1 operator) and general (POVM) measurement postulate (`QuantumTheory.POVM`, `QuantumTheory.prob`), with the Born rule's probabilities proved to sum to `1` (`sum_prob_eq_one`). Purification (`QuantumTheory.pure`) and purity (`QuantumTheory.purity`) defined, with `purity_pure : purity (pure ψ) = 1` proved. See `LeanCondensedMatter/QuantumTheory/DensityOperator.lean`. **Scoped to finite-dimensional `H`** — see the trace-class caveat in `notes/caveats.md`.

**In progress: infinite-dimensional density operators.** Now that Track C's `ContinuousLinearMap.trace` (with linearity/cyclicity) is done, extending `DensityOperator` beyond finite dimensions is underway in `LeanCondensedMatter/QuantumTheory/DensityOperatorTraceClass.lean` (namespace `QuantumTheory.TraceClass`, additive to the finite-dimensional file above — nothing there is touched). `QuantumTheory.TraceClass.DensityOperator` (positive + compact + trace-class + trace `1`) is defined, and `QuantumTheory.TraceClass.pure : State H → DensityOperator H` (the rank-one projector `|ψ⟩⟨ψ|`) is **fully proved** for arbitrary (possibly infinite-dimensional) `H`:
- `isCompactOperator_rankOne` — any rank-one operator `|x⟩⟨y|` is compact, via factoring through the locally-compact `ℂ`.
- `eigenspace_rankOne_eq_bot`/`eigenspace_rankOne_one` — for unit `ψ`, `|ψ⟩⟨ψ|`'s only nonzero eigenvalue is `1`, with eigenspace exactly `span {ψ}` (computed directly from the rank-one operator's formula, rather than via a general "finite rank" argument).
- `uniqueEigenvectorIndexRankOne` — consequently `EigenvectorIndex |ψ⟩⟨ψ|` has a *unique* element (every other eigenvalue's `Fin`-indexed fiber is empty), giving `rankOne_isTraceClass`/`rankOne_trace_eq_one` (trace-class, with trace exactly `1`, matching the physical `Tr[|ψ⟩⟨ψ|] = 1`) essentially for free.

Recurring Lean pitfall in this proof (not a math issue): `haveI hu := someDef args` makes `hu` an *opaque* local hypothesis, **not** definitionally equal to `someDef args` (unlike `let`) — so a later `show` restating the goal in terms of `someDef args` directly can fail to unify with a goal stated in terms of `hu`. Fix: either avoid the abbreviation and repeat `someDef args` at each use site, or use `let`/`set` (which preserve defeq) instead of `have`/`haveI` when you need to unfold back to the original term later.

**`POVM`/`prob`/`sum_prob_eq_one` are now ported (infinite-dimensional), in `QuantumTheory.TraceClass`.** The originally-anticipated blocker — `E_m ∘ ρ` need not be self-adjoint, so `ContinuousLinearMap.trace` doesn't directly apply — turned out to have a simpler resolution than the Hilbert–Schmidt inner product route developed for it (`notes/roadmaps/operator-algebra.md`): `prob` is defined directly via `ρ`'s *own* eigendecomposition (`ContinuousLinearMap.EigenvectorIndex`/`eigenvectorFamily`, from `Analysis/CompactSelfAdjoint.lean`) rather than via a general basis-independent trace of `E_m ∘ ρ`:
- `QuantumTheory.TraceClass.POVM` — a finite family of positive bounded operators summing to the identity. Unlike the finite-dimensional `QuantumTheory.POVM`, the individual `E m` need *not* be compact or trace-class (e.g. a single-outcome POVM forces `E () = 1`, never compact in infinite dimensions) — the definition only uses `ρ`'s trace-class-ness, not `E_m`'s.
- `QuantumTheory.TraceClass.prob P ρ m := (Σᵢ λᵢ ⟪eᵢ, E_m eᵢ⟫).re`, summing over `ρ`'s eigenvector family `e` with eigenvalues `λ`. Well-defined (`summable_prob_term`) by comparing `|λᵢ ⟪eᵢ,E_m eᵢ⟩| ≤ |λᵢ|·‖E_m‖` (each `eᵢ` a unit vector, `IsTraceClass ρ.op` giving `Σ|λᵢ|` summable) against the trace-class hypothesis.
- `QuantumTheory.TraceClass.sum_prob_eq_one` — proved by swapping the finite sum over outcomes `M` with the (absolutely convergent) sum over `ρ`'s eigenvectors (`Summable.tsum_finsetSum`), using `P.sum_eq_id` to collapse `Σₘ E_m eᵢ` back to `eᵢ` (via `⟪eᵢ,eᵢ⟩ = 1`, unit vectors), and `ρ.trace_eq_one` to evaluate the resulting eigenvalue sum.

This sidesteps needing `E_m` itself to be Hilbert–Schmidt (which the `innerHS`-based route would have required), since only `ρ`'s eigenbasis — not a general Hilbert basis — is ever used; the Hilbert–Schmidt inner product infrastructure (steps 1–4, complete) remains available for other purposes but wasn't needed for the Born rule after all.

**Still needed: `purity` (`Tr[ρ²]`) — deliberately deferred, not just unstarted.** `ρ ∘ ρ` is compact and self-adjoint for free, but proving it's *trace-class* needs a new spectral-theory lemma not yet in `Analysis/CompactSelfAdjoint.lean`: for self-adjoint `T`, `Module.End.eigenspace (T ∘ T) ν = Module.End.eigenspace T √ν` for `ν > 0` (simpler than the fully general statement since `ρ` is positive, so has no negative eigenvalues, ruling out the `eigenspace T (-√ν)` contribution that would otherwise also merge in). This is comparable in scope to the existing eigenvector-family machinery in that file, not a quick corollary — considered and consciously deferred (2026-07-14) in favor of other targets rather than attempted piecemeal.

**Von Neumann entropy is now ported (infinite-dimensional), in `LeanCondensedMatter/QuantumTheory/EntropyTraceClass.lean` (namespace `QuantumTheory.TraceClass`, additive to `QuantumTheory/Entropy.lean`).** `QuantumTheory.TraceClass.vonNeumannEntropy` computes `-Σᵢ λᵢ ln λᵢ` from `ρ`'s eigenvalues via `ContinuousLinearMap.EigenvectorIndex`, just as `prob` above does.

**A genuine mathematical wrinkle, not a Lean technicality:** unlike the finite-dimensional `ℝ`-valued `vonNeumannEntropy` (a finite sum, automatically finite), the infinite-dimensional entropy sum `Σᵢ (-λᵢ ln λᵢ)` — every term nonnegative — **can genuinely diverge** even though `Σᵢ λᵢ` converges (`ρ` is trace-class): e.g. `λᵢ = c/(i log² i)` is summable, but `-λᵢ ln λᵢ ~ c/(i log i)` is not. A trace-class density operator really can have infinite von Neumann entropy — this is standard in the physics literature, not a formalization artifact. So `vonNeumannEntropy` is **`ENNReal`-valued** (`[0, ∞]`) rather than `ℝ`-valued: the `tsum` is always well-defined in that codomain (divergence shows up honestly as `⊤`), avoiding the silent-junk-value-`0` problem a real-valued `tsum` would have for a non-summable sequence. `eigenvalue_nonneg` (needed to justify treating each `λᵢ` as a probability) is proved via Mathlib's `eigenvalue_nonneg_of_nonneg`, mirroring `ContinuousLinearMap.trace_nonneg`'s proof.

**Still needed:** `gibbsState`/`energyExpValue`/`helmholtzFreeEnergy_ge`/`vonNeumannEntropy_gibbsState` — the canonical-distribution target — are not yet ported; defining `gibbsState = e^{-βH}/Z(β)` for an infinite-dimensional Hamiltonian needs additional structure (e.g. a discrete-spectrum/compact-resolvent assumption on `Hop`) not yet formalized here.

## Von Neumann entropy / Boltzmann's principle (finite-dimensional)

Status: `stated`.

`QuantumTheory.vonNeumannEntropy` (`-Tr[ρ ln ρ]`, computed via the eigenvalues of `ρ`) defined. See `LeanCondensedMatter/QuantumTheory/Entropy.lean`. **Scope note:** only the mathematical quantity is defined; Boltzmann's principle itself (its equality, times `k_B`, with a thermodynamic entropy `S[U,V,N]`) is a postulate connecting to thermodynamics, which stays out of scope — see `notes/model-and-assumptions.md`. No theorems proved yet (e.g. nonnegativity, or entropy `0` for pure states) — natural next steps if this target is picked up again.

## Canonical distribution as the Helmholtz free-energy-minimizing state

Status: `stated`.

Goal: formalize that the canonical/Gibbs state `ρ' = e^{-βH}/Z(β)`, `Z(β) = Tr[e^{-βH}]`, is the (unconstrained) minimizer of the Helmholtz free energy `F[ρ] = Tr[ρĤ] - (1/β)·vonNeumannEntropy ρ` over all density operators `ρ` — *not* "the entropy-maximizing state at fixed energy" (an earlier, less precise phrasing of this target; the free-energy formulation is the one actually derived from Gibbs–Klein, with no separate energy constraint needed). Needed for the finite-temperature theory: this is what identifies `Z(β) = Tr[e^{-βH}]` (used throughout the Linked Cluster Theorem target) as *the* physically realized state, not just a convenient definition.

`QuantumTheory.helmholtzFreeEnergy_ge` — **proved** (`LeanCondensedMatter/QuantumTheory/Entropy.lean`): for any density operator `ρ`, Hamiltonian `Hop : Observable H`, and `β > 0`,
`-(1/β)·ln Z(β) ≤ energyExpValue ρ Hop - (1/β)·vonNeumannEntropy ρ`, i.e. `F[ρ] ≥ -(1/β)·ln Z(β)`. The proof avoids the originally-anticipated blocker (relating `gibbsState`'s spectral data to Mathlib's canonical sorted eigenbasis): it runs the Gibbs–Klein argument directly against `Hop`'s own eigenbasis, using Boltzmann weights `w_k = e^{-βEₖ}/Z(β)` as plain functions rather than routing through `gibbsState`/`relEntropy` at all, sidestepping the correspondence problem entirely. `energyExpValue` (`Tr[ρĤ]`) and its cross-eigenbasis double-sum expansion (`energyExpValue_eq_sum`) were added to support this.

`QuantumTheory.diagOp_eigenvalues_map_eq` — **proved** (`LeanCondensedMatter/QuantumTheory/Entropy.lean`): a general lemma showing that for a self-adjoint operator presented diagonally as `∑ i, w i • |bᵢ⟩⟨bᵢ|` in a known orthonormal basis `b`, the multiset of weights `w` equals the multiset of the operator's own Mathlib-sorted spectral eigenvalues — proved via the characteristic polynomial (basis-independent, `LinearMap.charpoly_toMatrix`) rather than by exhibiting an explicit reindexing permutation. This closes the originally-anticipated blocker directly (rather than avoiding it as `helmholtzFreeEnergy_ge` did).

`QuantumTheory.vonNeumannEntropy_gibbsState` — **proved**: `vonNeumannEntropy hn (gibbsState hn Hop β) = β · energyExpValue (gibbsState hn Hop β) Hop + ln Z(β)`, i.e. `gibbsState`'s own Helmholtz free energy is exactly `-(1/β)·ln Z(β)` — the lower bound of `helmholtzFreeEnergy_ge` is attained by `gibbsState` itself. Uses `diagOp_eigenvalues_map_eq` to identify `gibbsState`'s own spectral data with its Boltzmann weights without an explicit permutation.

**Remaining to close this target fully:** the equality-iff-`ρ = gibbsState` direction (uniqueness of the minimizer) is not yet formalized — only that the bound is achieved (by `gibbsState`) and always valid (`helmholtzFreeEnergy_ge`) are proved.

## Basic quantum field theory formalization

Status: `idea`.

Prerequisite groundwork target: the minimal scaffolding needed before stating either theorem below — e.g. creation/annihilation operator algebra (CCR/CAR), Fock space construction, and normal ordering, on the countably infinite-dimensional lattice setting chosen for this project. Precise scope to be filled in `notes/model-and-assumptions.md`.

## Finite-temperature Bloch–de Dominicis theorem

Status: `idea`.

Goal: formalize the thermal-average analogue of Wick's theorem — that a thermal expectation value of a product of creation/annihilation operators decomposes into a sum over all full pairings (contractions), each a product of two-operator thermal averages. Depends on the QFT groundwork target above.
