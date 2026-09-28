---
status: accepted
---

# Keep finite-band Berry geometry upstream of physical models

Represent finite-dimensional spectral geometry at one parameter point with a self-adjoint Hamiltonian, a finite orthonormal eigenbasis and real spectrum, and explicit directional derivative data satisfying the differentiated eigenpair and orthonormality identities. Prove Hellmann–Feynman, Born–Fock under explicit nondegeneracy, Berry curvature, and its force-matrix expression in `Analysis`, independently of AHE, disorder, and second quantization.

Do not require a global smooth eigenvector selection or gauge patch to use these pointwise identities. With `Aᵘₘₙ = i ⟨φₘ, ∂ᵤ φₙ⟩`, the full band-index Berry-connection matrix is Hermitian; only its diagonal entries are real. Fix curvature signs and index order by the generic Lean theorem and its concrete model consumer. Keep global Berry phases, topology, and degenerate-band generalizations downstream until a consumer needs them.

The generic spectral-geometry layer does not implement response regularization. Kubo/resolvent consumers own broadening and adiabatic conventions; formal unregularized oscillatory integrals are not substitutes for that boundary.

Evidence: [Berry geometry umbrella](../../LeanCondensedMatter/Analysis/Operator/BerryGeometry.lean), [pointwise eigenbasis data and connection](../../LeanCondensedMatter/Analysis/Operator/BerryGeometry/Connection.lean), [curvature and force-matrix formula](../../LeanCondensedMatter/Analysis/Operator/BerryGeometry/Curvature.lean), and the [massive-Dirac consumer](../../LeanCondensedMatter/Transport/Models/MassiveDirac/Model/Berry/Bridge.lean).

## Historical evidence

[Issue #1310](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1310) completed the generic finite-band layer and verified its sign/index convention through the massive-Dirac consumer. The implemented scope is pointwise nondegenerate geometry; global smooth gauges, Berry phase along paths, topology, and degenerate/non-Abelian extensions remain optional work rather than hidden assumptions.
