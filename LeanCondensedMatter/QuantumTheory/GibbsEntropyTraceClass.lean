import LeanCondensedMatter.QuantumTheory.HelmholtzFreeEnergyTraceClass

/-!
# Gibbs-state entropy equality via trace-class operators

This file develops the equality case of the trace-class Helmholtz free-energy inequality for the
normalized Gibbs state. Under the current bounded-Hamiltonian API, compactness of the Gibbs
operator forces the ambient Hilbert space to be finite-dimensional; that fact is used only to
discharge summability of the Gibbs state's entropy operator.
-/

namespace QuantumTheory.TraceClass

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The entropy operator of the normalized Gibbs state has summable nonzero real eigenvalues.
For the current bounded notion of Hamiltonian this follows from compactness of the Gibbs operator,
which forces `H` to be finite-dimensional. -/
theorem gibbsState_entropyOp_hasSummableRealEigenvalues (Hop : Observable H) (β : ℝ)
    (hcompact : IsCompactOperator (gibbsOp Hop β))
    (hsummable : HasSummableRealEigenvalues (gibbsOp Hop β))
    (hZ : spectralTrace hsummable ≠ 0) :
    HasSummableRealEigenvalues (entropyOp (gibbsState Hop β hcompact hsummable hZ)) := by
  letI := finiteDimensional_of_gibbsOp_isCompact Hop β hcompact
  exact Summable.of_finite

end QuantumTheory.TraceClass
