# Roadmap — Linked Cluster Theorem (combined, depends on both tracks)

See [notes/roadmap.md](../roadmap.md) for the status table and how this fits into the overall plan.

## Linked Cluster Theorem (finite temperature)

Status: `idea`.

Goal: formalize the statement that `log Z` (thermal/Matsubara perturbation theory, `Z = tr e^{-βH}`) admits a cumulant expansion containing only connected-diagram contributions, on a countably infinite-dimensional lattice model. Depends on all of Track A (Bloch–de Dominicis pairing structure), Track B (moment-cumulant formula, connectedness), and Track D (second quantization: Fock space, creation/annihilation, CCR, Hamiltonians, Dyson expansion — see [notes/roadmaps/second-quantization.md](second-quantization.md)). See `notes/model-and-assumptions.md` for the full setup and the scope note on convergence/trace-class questions (deliberately excluded — the combinatorial core is treated as a formal/algebraic identity).

**Near-term target (algebraic, Track D's endpoint):** `QuantumLinkedCluster.lean` — apply Track B's `mu_eq_prod_restrict` (already proved) to a Dyson-expanded `log Z` built from Track D's Hamiltonians, giving the algebraic Linked Cluster Theorem before any Hilbert-space analytic issues (completion, self-adjointness, spectral theory) are addressed.

Remaining building block once all tracks land: (1) definition of thermal expectation values and their cumulants, (2) a notion of "connected" for set partitions / diagrams matching the physics definition, connecting Track A's pairings to Track B's partitions.
