# Roadmap — Quantum theory foundations (Track A)

See [notes/roadmap.md](../roadmap.md) for the status table and how this track fits into the overall plan.

## Minimal axiomatic quantum theory foundation

Status: `stated`.

State-space postulate and observable definition (`QuantumTheory.State`, `QuantumTheory.Observable`) and the expectation value they define, with reality of expectation values proved (`expValue_im_eq_zero`) and phase indeterminacy proved (`expValue_smul_of_norm_eq_one`). See `LeanCondensedMatter/QuantumTheory/Postulates.lean` and `notes/model-and-assumptions.md`. Entry point beneath the QFT groundwork target below.

## Density operators and the Born rule (finite-dimensional)

Status: `stated`.

Density-operator postulate (`QuantumTheory.DensityOperator`, positive trace-1 operator) and general (POVM) measurement postulate (`QuantumTheory.POVM`, `QuantumTheory.prob`), with the Born rule's probabilities proved to sum to `1` (`sum_prob_eq_one`). Purification (`QuantumTheory.pure`) and purity (`QuantumTheory.purity`) defined, with `purity_pure : purity (pure ψ) = 1` proved. See `LeanCondensedMatter/QuantumTheory/DensityOperator.lean`. **Scoped to finite-dimensional `H`** — see the trace-class caveat in `notes/caveats.md`; extending to the countably-infinite lattice setting used elsewhere in this roadmap needs that gap closed first.

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
