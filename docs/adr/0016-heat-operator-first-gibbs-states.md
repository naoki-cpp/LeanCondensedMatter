---
status: accepted
---

# Normalize heat data before constructing the Gibbs state

Make the Gibbs-state boundary positive heat data `Kβ`, supplied with general trace-class evidence and a nonzero condition. Normalize it through the canonical `DensityOperator.normalizePositive`; do not add a second `HeatOperator` state wrapper. This permits bounded and countable pure-point constructions to share one state boundary.

The quantum Gibbs layer consumes the heat operator and its verified properties. Constructing `Kβ = exp(-βH)` from a semibounded unbounded self-adjoint Hamiltonian belongs to upstream domain-aware operator analysis, not to a formal exponential over bounded operators. A countable pure-point model is a proved specialization with explicit Boltzmann and energy-integrability assumptions. Entropy and variational conclusions carry their own finiteness conditions; the diagonal/classical minimizer theorem does not imply the fully quantum noncommuting unbounded result.

The bounded-Hamiltonian Gibbs API is explicitly finite-dimensional. Compactness of the invertible bounded Gibbs operator forces finite dimension. Genuine infinite-dimensional examples therefore come from trace-class heat data such as summable diagonal weights, not from weakening the bounded API. Thermodynamic limits remain separate.

Evidence: [positive normalization](../../LeanCondensedMatter/QuantumTheory/DensityOperator/Normalize.lean), [heat-operator Gibbs boundary](../../LeanCondensedMatter/QuantumTheory/Gibbs/HeatOperator.lean), and [countable pure-point specialization](../../LeanCondensedMatter/QuantumTheory/Gibbs/Eigenbasis.lean).
