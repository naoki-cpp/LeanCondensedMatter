import LeanCondensedMatter.QuantumTheory.HelmholtzFreeEnergyTraceClass
import LeanCondensedMatter.QuantumTheory.FiniteDensityOperatorExpectationTraceClass

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

/-- The normalized Gibbs state acts diagonally on every energy eigenvector. -/
theorem gibbsState_apply_eigenvector (Hop : Observable H) (β : ℝ)
    (hcompact : IsCompactOperator (gibbsOp Hop β))
    (hsummable : HasSummableRealEigenvalues (gibbsOp Hop β))
    (hZ : spectralTrace hsummable ≠ 0) {v : H} {E : ℝ}
    (hv : (Hop.1 : H →ₗ[ℂ] H) v = (E : ℂ) • v) :
    (gibbsState Hop β hcompact hsummable hZ).op v =
      (((spectralTrace hsummable)⁻¹ : ℝ) • (Real.exp (-β * E) : ℂ)) • v := by
  change ((spectralTrace hsummable)⁻¹ • gibbsOp Hop β) v = _
  rw [smul_apply, gibbsOp_apply_eigenvector Hop β hv]
  exact (smul_assoc ((spectralTrace hsummable)⁻¹ : ℝ)
    (Real.exp (-β * E) : ℂ) v).symm

/-- In finite dimensions, the trace-class energy expectation agrees with the usual real part of
`Tr(ρ H)`. -/
theorem energyExpValue_eq_re_linearMap_trace [FiniteDimensional ℂ H]
    (ρ : DensityOperator H) (Hop : Observable H) :
    energyExpValue ρ Hop =
      (LinearMap.trace ℂ H ((ρ.op ∘L Hop.1 : H →L[ℂ] H) : H →ₗ[ℂ] H)).re := by
  simpa [energyExpValue] using congrArg Complex.re (ρ.expectation_eq_linearMap_trace Hop.1)

/-- The entropy operator of the normalized Gibbs state has summable nonzero real eigenvalues.
For the current bounded notion of Hamiltonian this follows from compactness of the Gibbs operator,
which forces `H` to be finite-dimensional. -/
theorem gibbsState_entropyOp_hasSummableRealEigenvalues (Hop : Observable H) (β : ℝ)
    (hcompact : IsCompactOperator (gibbsOp Hop β))
    (hsummable : HasSummableRealEigenvalues (gibbsOp Hop β))
    (hZ : spectralTrace hsummable ≠ 0) :
    HasSummableRealEigenvalues (entropyOp (gibbsState Hop β hcompact hsummable hZ)) := by
  letI := finiteDimensional_of_gibbsOp_isCompact Hop β hcompact
  let ρ := gibbsState Hop β hcompact hsummable hZ
  have hEntropyCompact : IsCompactOperator (entropyOp ρ) := entropyOp_isCompact ρ
  have hEntropySelfAdjoint : IsSelfAdjoint (entropyOp ρ) := by
    rw [entropyOp]
    exact cfc_predicate _ _
  letI : Finite (EigenvectorIndex (entropyOp ρ)) :=
    (orthonormal_eigenvectorFamily hEntropyCompact hEntropySelfAdjoint.isSymmetric).linearIndependent.finite
  exact Summable.of_finite

end QuantumTheory.TraceClass
