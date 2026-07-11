# Models and Assumptions

Physical models under consideration, their assumptions, and how each maps to a formal definition. Every entry must cite its source and name the corresponding Lean declarations once they exist.

## Models

### Finite-temperature Linked Cluster Theorem

- **Hilbert space / algebra setting:** countably infinite-dimensional, lattice model (e.g. spins or fermions/bosons on a countable lattice). Chosen for physical realism over the finite-dimensional alternative.
- **Statement level:** the cumulant expansion of `log Z` (with `Z = tr e^{-βH}`, thermal/Matsubara perturbation theory) contains only connected-diagram contributions. This is the standard formulation of the theorem.
- **Proof strategy:** derive from a general combinatorial moment-cumulant theorem (set-partition lattice / Möbius function on the partition lattice), then specialize to the thermal expectation-value setting, rather than proving it directly from Dyson series + Wick's theorem.

### Minimal axiomatic quantum theory foundation

- **Role:** entry point beneath the QFT groundwork target — the bare state-space postulate and observable definition, before second quantization / field content is introduced.
- **State space postulate:** a pure state is a unit vector in a complex Hilbert space (`QuantumTheory.State`, `LeanCondensedMatter/QuantumTheory/Postulates.lean`). This is a genuine postulate (an independent physical assumption). Global-phase equivalence of states is not yet formalized: `State H` is a space of representatives, not of physical (phase-equivalence-class) states — see `notes/caveats.md`.
- **Observable (definition, not a postulate):** an observable is *defined* as a self-adjoint bounded linear operator on the state space (`QuantumTheory.Observable`). Self-adjointness is the defining property, not an independently assumed axiom — it is exactly what makes expectation values real (`expValue_im_eq_zero`). Built on Mathlib's `IsSelfAdjoint` / `ContinuousLinearMap.adjoint`.
- **Expectation value:** `QuantumTheory.expValue A ψ = ⟪A ψ, ψ⟫`; proved real (`expValue_im_eq_zero`) via Mathlib's `LinearMap.IsSymmetric.im_inner_apply_self`, as required for it to represent a measurable quantity.
- **Phase indeterminacy:** multiplying a state by a unit-modulus complex number does not change any observable's expectation value (`expValue_smul_of_norm_eq_one`) — the physical content behind treating `State H` as a space of representatives (see above).

### Density operators and the Born rule

- **Role:** extends the pure-state picture above to statistical mixtures, and gives the general (POVM) measurement postulate. Restricted to finite-dimensional `H` — see the trace-class caveat in `notes/caveats.md`.
- **Density operator postulate:** the state of a system is a positive operator of trace `1` (`QuantumTheory.DensityOperator`, `LeanCondensedMatter/QuantumTheory/DensityOperator.lean`).
- **General measurement postulate (Born rule):** a POVM (`QuantumTheory.POVM`, a finite family of positive operators summing to the identity) assigns outcome probabilities `QuantumTheory.prob P ρ m = Tr[E_m ρ]`; proved to sum to `1` over outcomes (`sum_prob_eq_one`).
- **Purification:** `QuantumTheory.pure ψ = |ψ⟩⟨ψ|` maps a pure state (`QuantumTheory.State`) to its density-operator representative, via Mathlib's `InnerProductSpace.rankOne`.
- **Purity:** `QuantumTheory.purity ρ = Tr[ρ²]`; proved equal to `1` on `pure ψ` (`purity_pure`). General bounds `0 < purity ≤ 1` (relying on spectral decomposition) are not yet formalized — out of scope for now.

### Basic quantum field theory formalization

- **Role:** shared prerequisite for both the Linked Cluster Theorem and the Bloch–de Dominicis theorem targets, not a physics result in its own right. Scope kept to what those two targets actually need — not a general-purpose QFT library.
- **Setting:** consistent with the lattice model chosen above — creation/annihilation operators indexed by lattice site (and internal degrees of freedom as needed), CCR (bosons) or CAR (fermions) relations, Fock space as the representation space.
- **Open scope questions (to resolve before formal definitions are written):** bosons, fermions, or both; whether Fock space is built directly or assumed via an existing Mathlib/Lean construction if one exists; how normal ordering is defined for the infinite-lattice case given the convergence caveat below.

### Finite-temperature Bloch–de Dominicis theorem

- **Statement level:** thermal expectation value of a product of creation/annihilation operators equals the sum over all full pairings (contractions) of the product of pairwise thermal averages — the thermal-average generalization of Wick's theorem.
- **Relation to Linked Cluster Theorem:** expected to serve as an input lemma to the Linked Cluster Theorem's diagrammatic expansion (pairings ↔ diagrams), but the precise logical dependency is not yet fixed — record the decision here once made.
- **Convergence:** subject to the same caveat as the Linked Cluster Theorem below — treated first as an algebraic identity for a fixed finite sub-volume / finite operator product, not as an analytic statement about infinite sums.

## Assumptions

### Finite-temperature Linked Cluster Theorem

- **Convergence is out of scope for the combinatorial core.** The moment-cumulant identity from the partition lattice is a formal/algebraic identity (holds order-by-order in the perturbative expansion, or as an identity of formal power series). It does not by itself establish convergence of the series to `log Z`, nor trace-class properties of the infinite-lattice operators. Analytic questions (existence/convergence of the thermodynamic limit, trace-class-ness of `e^{-βH}`) are a separate concern to be scoped later — record any such follow-up target separately in `notes/roadmap.md` rather than folding it into this one.
- **Consequence for scope:** the initial target theorem should be stated as an algebraic identity between the cumulants of `log Z`'s expansion and connected diagrams (or connected set partitions), conditioned on the underlying moments/cumulants being well-defined (e.g. as formal power series, or for a fixed finite sub-volume before any thermodynamic limit is taken).

## Physics-to-Lean dictionary

| Physical notion | Formal counterpart | Source |
|---|---|---|
| Pure state | `QuantumTheory.State H` | `LeanCondensedMatter/QuantumTheory/Postulates.lean` |
| Observable | `QuantumTheory.Observable H` | `LeanCondensedMatter/QuantumTheory/Postulates.lean` |
| Expectation value `⟨ψ\|A\|ψ⟩` | `QuantumTheory.expValue A ψ` | `LeanCondensedMatter/QuantumTheory/Postulates.lean` |
| Density operator / mixed state | `QuantumTheory.DensityOperator H` | `LeanCondensedMatter/QuantumTheory/DensityOperator.lean` |
| POVM | `QuantumTheory.POVM H M` | `LeanCondensedMatter/QuantumTheory/DensityOperator.lean` |
| Born-rule probability `Tr[E_m ρ]` | `QuantumTheory.prob P ρ m` | `LeanCondensedMatter/QuantumTheory/DensityOperator.lean` |
| Pure state `\|ψ⟩⟨ψ\|` (density-operator form) | `QuantumTheory.pure ψ` | `LeanCondensedMatter/QuantumTheory/DensityOperator.lean` |
| Purity `Tr[ρ²]` | `QuantumTheory.purity ρ` | `LeanCondensedMatter/QuantumTheory/DensityOperator.lean` |
