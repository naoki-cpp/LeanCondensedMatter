# Models and Assumptions

Physical models under consideration, their assumptions, and how each maps to a formal definition. Every entry must cite its source and name the corresponding Lean declarations once they exist.

## Models

### Finite-temperature Linked Cluster Theorem

- **Hilbert space / algebra setting:** countably infinite-dimensional, lattice model (e.g. spins or fermions/bosons on a countable lattice). Chosen for physical realism over the finite-dimensional alternative.
- **Statement level:** the cumulant expansion of `log Z` (with `Z = tr e^{-βH}`, thermal/Matsubara perturbation theory) contains only connected-diagram contributions. This is the standard formulation of the theorem.
- **Proof strategy:** derive from a general combinatorial moment-cumulant theorem (set-partition lattice / Möbius function on the partition lattice), then specialize to the thermal expectation-value setting, rather than proving it directly from Dyson series + Wick's theorem.
- **Mathlib survey for Track B (partition-lattice Möbius / moment-cumulant):** `Mathlib.Order.Partition.Finpartition` gives the set-partition lattice with exactly the refinement order needed (`P ≤ Q` iff every block of `P` sits in a block of `Q`), plus `OrderBot`/`Fintype`. `Mathlib.Combinatorics.Enumerative.IncidenceAlgebra` gives a general Möbius function (`IncidenceAlgebra.mu`) and Möbius inversion theorem (`moebius_inversion_top`/`bot`) for any `PartialOrder` + `LocallyFiniteOrder`. **Missing and must be built:** (1) a `LocallyFiniteOrder (Finpartition s)` instance — the key adapter connecting the two, not present in Mathlib; (2) the closed-form partition-lattice Möbius function `μ(π,σ) = (-1)^(|π|-|σ|) ∏(n_B-1)!`; (3) the exponential-formula / moment-cumulant relation over set partitions — Mathlib has no general EGF (exponential generating function) framework at all (checked; only `PowerSeries.exp` exists as a raw ingredient). None of (1)–(3) exist in any Lean library found (Mathlib or otherwise) as of this check.

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

### Von Neumann entropy / Boltzmann's principle

- **Role:** extends the density-operator picture above with entropy. Restricted to finite-dimensional `H`, for the same reason as `DensityOperator`.
- **Von Neumann entropy (defined):** `QuantumTheory.vonNeumannEntropy ρ = -Tr[ρ ln ρ] = Σᵢ negMulLog(λᵢ)` over the eigenvalues `λᵢ` of `ρ` (`LeanCondensedMatter/QuantumTheory/Entropy.lean`), using Mathlib's `LinearMap.IsSymmetric.eigenvalues` and `Real.negMulLog`.
- **Boltzmann's principle (postulate, not formalized):** `k_B` times the von Neumann entropy equals the thermodynamic entropy `S[U,V,N]`. This equates a formal quantum-mechanical quantity with a thermodynamic one; since thermodynamics proper is out of scope for this project (see the Linked Cluster Theorem scope note above), the postulate's *equality claim* is not formalized — only its LHS (`vonNeumannEntropy`) is.
- **Equal a priori probabilities postulate (not formalized):** at equilibrium, the state realized is the one minimizing the Helmholtz free energy (equivalently: maximizing the *combined* entropy of the system plus the heat bath it exchanges energy with — not simply "maximizing the system's own entropy at fixed energy", a looser phrasing corrected during this work). Not yet formalized as a general variational principle; the free-energy inequality itself is derived directly from Gibbs–Klein below without needing to formalize "maximization" as its own concept. Feeds directly into the "Canonical distribution as the Helmholtz free-energy-minimizing state" target below.

### Canonical distribution as the Helmholtz free-energy-minimizing state

- **Role:** identifies the canonical/Gibbs state `ρ' = e^{-βH}/Z(β)` as the state that is actually physically realized at equilibrium, rather than an arbitrary convenient choice. This is what justifies treating `Z(β) = Tr[e^{-βH}]` as *the* object of interest in the Linked Cluster Theorem target.
- **Statement (corrected during this work):** the precise claim is that `ρ' = e^{-βH}/Z(β)` minimizes the Helmholtz free energy `F[ρ] = Tr[ρĤ] - (1/β)·vonNeumannEntropy ρ` over **all** density operators `ρ` — an *unconstrained* minimization, not "maximize entropy subject to fixed expected energy" (an earlier, imprecise phrasing of this target that this note corrects). No Lagrange-multiplier/energy-constraint machinery is needed; the free-energy inequality follows directly from Gibbs–Klein applied to `ρ` and `ρ'` together with the fact that `ρ'` is diagonal in `Ĥ`'s own eigenbasis (so `Tr[ρ ln ρ']` reduces to a linear functional of `Tr[ρĤ]`).
- **Proof strategy (Gibbs–Klein):** `Tr[ρ ln ρ] ≥ Tr[ρ ln ρ']` for any density operator `ρ` and Gibbs-form `ρ'`, with equality iff `ρ = ρ'`. This is a quantum (matrix) analogue of Gibbs' inequality for classical relative entropy. Combined with `Tr[ρ ln ρ'] = -β·Tr[ρĤ] - ln Z(β)` (using `ρ'`'s diagonal form) and `Tr[ρ ln e^{βĤ}] = β·Tr[ρĤ]`, this rearranges directly into `F[ρ] ≥ -ln Z(β)/β = F[ρ']`.
- **Gap (closed for the restricted case):** Mathlib has no Klein-type trace inequality / quantum relative entropy machinery (checked — not present as of the pinned revision). Built directly in `LeanCondensedMatter/QuantumTheory/Entropy.lean` as `relEntropy`/`relEntropy_nonneg`, via spectral decomposition of both `ρ` and `ρ'` and `ln x ≤ x - 1`, following the same proof structure as the physics reference used for this project.
- **Canonical state — constructed:** `QuantumTheory.partitionFunction hn Hop β = Σᵢ e^{-βEᵢ}` and `QuantumTheory.gibbsState hn Hop β = Σᵢ (e^{-βEᵢ}/Z(β)) • |bEᵢ⟩⟨bEᵢ|` (`Eᵢ`, `bEᵢ` = `Hop`'s eigenvalues/eigenbasis), proved to be a valid `DensityOperator` (`IsPositive`, trace `1`) via `Real.exp`'s positivity and `Σᵢ e^{-βEᵢ}/Z(β) = 1` by construction.
- **Junk-value caveat driving the "full support" reasoning:** `relEntropy_nonneg` requires `∀ k, 0 < q k` (the second operator's eigenvalues all strictly positive), *not* just nonnegative. Reason: Lean's `Real.log 0 = 0` (a junk-value convention) is not the mathematically-correct `-∞`, so the per-term bound `p_m ln(p_m/q_k) ≥ p_m - q_k` used in the classical proof genuinely fails in Lean when `p_m > 0` and `q_k = 0` (whereas classically this case is vacuous because the LHS is `+∞`). `ρ`'s own eigenvalues are *not* required to be positive (`p_m = 0` terms are handled fine, contributing `0 ≤ -q_k · c_{mk}` trivially) — density operators are only positive *semi*-definite in general (e.g. `pure ψ` has eigenvalues `{1,0,…,0}`), so this asymmetry is intentional, not an oversight. The intended application's Boltzmann weights `e^{-βEᵢ}/Z(β)` are unconditionally positive (the exponential is always positive), so this restriction is never actually binding.
- **Route taken for `helmholtzFreeEnergy_ge` — bypasses the `gibbsState`/canonical-eigenbasis correspondence problem entirely:** rather than proving `gibbsState`'s Mathlib-canonical (sorted) `eigenvalues`/`eigenvectorBasis` coincide with its hand-built spectral data (`Eᵢ`, `bEᵢ` from `Hop`) — a real but avoidable piece of work — `helmholtzFreeEnergy_ge` re-derives the Klein-inequality argument from scratch inside its own proof, working directly with `Hop`'s eigenbasis and the plain function `w k := e^{-βEₖ}/Z(β)` (never constructing an actual `DensityOperator` for the second operand). This is legitimate because the Gibbs–Klein proof only ever needs "an orthonormal basis + a positive probability-summing-to-one weight function," not that the weights/basis are literally `ρ.2.1.isSymmetric`'s own canonical data for some specific density operator. `QuantumTheory.energyExpValue` (`Tr[ρĤ]`, defined via `LinearMap.trace` of the composed operator) and `energyExpValue_eq_sum` (its expansion via `ρ`'s and `Hop`'s *separate* eigenbases, since they need not commute — proved via `LinearMap.trace_eq_sum_inner` with `Hop`'s eigenbasis, then expanding vectors of that basis in `ρ`'s eigenbasis via `OrthonormalBasis.sum_repr'`) supply the energy term.

### Basic quantum field theory formalization

- **Role:** shared prerequisite for both the Linked Cluster Theorem and the Bloch–de Dominicis theorem targets, not a physics result in its own right. Scope kept to what those two targets actually need — not a general-purpose QFT library.
- **Setting:** consistent with the lattice model chosen above — creation/annihilation operators indexed by lattice site (and internal degrees of freedom as needed), CCR (bosons) or CAR (fermions) relations, Fock space as the representation space.
- **Open scope questions (to resolve before formal definitions are written):** bosons, fermions, or both; whether Fock space is built directly or assumed via an existing Mathlib/Lean construction if one exists; how normal ordering is defined for the infinite-lattice case given the convergence caveat below.

### Finite-temperature Bloch–de Dominicis theorem

- **Statement level:** thermal expectation value of a product of creation/annihilation operators equals the sum over all full pairings (contractions) of the product of pairwise thermal averages — the thermal-average generalization of Wick's theorem.
- **Relation to Linked Cluster Theorem:** expected to serve as an input lemma to the Linked Cluster Theorem's diagrammatic expansion (pairings ↔ diagrams), but the precise logical dependency is not yet fixed — record the decision here once made.
- **Convergence:** subject to the same caveat as the Linked Cluster Theorem below — treated first as an algebraic identity for a fixed finite sub-volume / finite operator product, not as an analytic statement about infinite sums.
- **Reference only, not a dependency:** the external Lean library PhysLean formalizes the zero-temperature (vacuum expectation value) Wick's theorem (`wicks_theorem`, over a `WickContraction` type representing pairings, with sign/statistics bookkeeping). Decided not to add PhysLean as a project dependency — it proves the wrong (zero-temperature) statement and pulls in a large amount of unrelated QFT infrastructure. `WickContraction`'s combinatorial *shape* (as a type of pairings) may be worth consulting as design inspiration when defining the thermal-average pairing structure here, but the proof itself needs to be written independently for the thermal-average setting.

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
| Von Neumann entropy `-Tr[ρ ln ρ]` | `QuantumTheory.vonNeumannEntropy ρ` | `LeanCondensedMatter/QuantumTheory/Entropy.lean` |
| Quantum relative entropy `Tr[ρ ln ρ] - Tr[ρ ln ρ']` | `QuantumTheory.relEntropy ρ ρ'` | `LeanCondensedMatter/QuantumTheory/Entropy.lean` |
| Partition function `Z(β) = Tr[e^{-βH}]` | `QuantumTheory.partitionFunction hn Hop β` | `LeanCondensedMatter/QuantumTheory/Entropy.lean` |
| Canonical (Gibbs) state `e^{-βH}/Z(β)` | `QuantumTheory.gibbsState hn Hop β` | `LeanCondensedMatter/QuantumTheory/Entropy.lean` |
| Energy expectation value `Tr[ρĤ]` | `QuantumTheory.energyExpValue ρ Hop` | `LeanCondensedMatter/QuantumTheory/Entropy.lean` |
| Helmholtz free energy `Tr[ρĤ] - (1/β)S[ρ]` | `energyExpValue ρ Hop - (1/β) * vonNeumannEntropy hn ρ` (RHS of `helmholtzFreeEnergy_ge`) | `LeanCondensedMatter/QuantumTheory/Entropy.lean` |
