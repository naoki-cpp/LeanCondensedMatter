---
status: accepted
---

# Keep finite-band Berry geometry upstream of physical models

Represent finite-dimensional spectral geometry at one parameter point with a self-adjoint Hamiltonian, a finite orthonormal eigenbasis and real spectrum, and explicit directional derivative data satisfying the differentiated eigenpair and orthonormality identities. Prove Hellmann–Feynman, Born–Fock under explicit nondegeneracy, Berry curvature, and its force-matrix expression in `Analysis`, independently of AHE, disorder, and second quantization.

Do not require a global smooth eigenvector selection or gauge patch to use these pointwise identities. With `Aᵘₘₙ = i ⟨φₘ, ∂ᵤ φₙ⟩`, the full band-index Berry-connection matrix is Hermitian; only its diagonal entries are real. Fix curvature signs and index order by the generic Lean theorem and its concrete model consumer. Keep global phases and topology downstream from this pointwise API: a periodic-transport consumer must supply the lattice, integration, and global-topology structure, and pointwise identities alone imply no global invariant. Degenerate-band generalizations likewise remain downstream until a consumer needs them.

The generic spectral-geometry layer does not implement response regularization. Kubo/resolvent consumers own broadening and adiabatic conventions; formal unregularized oscillatory integrals are not substitutes for that boundary.

A concrete two-band model should provide its pointwise spectral adapter under an explicit nondegeneracy condition, then prove that the generic curvature agrees with both its gauge-independent projector/force-matrix expression and its closed-form benchmark. Route at least one physical consumer through the generic curvature so the model formula is a specialization of the shared API rather than a parallel theory. The MassiveDirac construction is restricted to `energy ≠ 0`; it adds no global gauge or topology result.

For a simple finite spectrum, construct the pointwise eigenvector derivatives algebraically from the eigenbasis and self-adjoint Hamiltonian derivatives using the parallel-transport gauge convention. Keep this as a pointwise constructor, not an explicit globally smooth eigenvector choice or a model-specific gauge-differentiation API.

Keep parameter-dependent finite-dimensional Berry connection and curvature behind the dedicated `Analysis.Operator.BerryGeometry` route. `Analysis.Operator.Spectral` owns generic eigenvector-family and resolvent results and must not acquire Berry dependencies; the broader `Analysis.Operator` umbrella may expose both independent routes for convenience.

Evidence: [Berry geometry umbrella](../../LeanCondensedMatter/Analysis/Operator/BerryGeometry.lean), [pointwise eigenbasis data and connection](../../LeanCondensedMatter/Analysis/Operator/BerryGeometry/Connection.lean), [curvature and force-matrix formula](../../LeanCondensedMatter/Analysis/Operator/BerryGeometry/Curvature.lean), and the [massive-Dirac consumer](../../LeanCondensedMatter/Models/MassiveDirac/Model/Berry/Bridge.lean).
