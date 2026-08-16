import LeanCondensedMatter.QuantumTheory.Gibbs.FreeEnergy
import LeanCondensedMatter.QuantumTheory.Entropy.Finite

/-!
# Gibbs-state entropy

Equality-side lemmas for the normalized Gibbs state. Under the bounded-Hamiltonian API, compactness
of the Gibbs operator forces finite dimension and hence entropy summability.
-/

namespace QuantumTheory

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The normalized Gibbs state acts diagonally on every energy eigenvector. -/
theorem gibbsState_apply_eigenvector (Hop : Observable H) (β : ℝ)
    (hcompact : IsCompactOperator (gibbsOp Hop β))
    (hsummable : HasSummableRealEigenvalues (gibbsOp Hop β))
    (hZ : spectralTrace (gibbsOp Hop β) ≠ 0) {v : H} {E : ℝ}
    (hv : (Hop.1 : H →ₗ[ℂ] H) v = (E : ℂ) • v) :
    (gibbsState Hop β hcompact hsummable hZ).op v =
      (((spectralTrace (gibbsOp Hop β))⁻¹ : ℝ) • (Real.exp (-β * E) : ℂ)) • v := by
  change ((spectralTrace (gibbsOp Hop β))⁻¹ • gibbsOp Hop β) v = _
  rw [smul_apply, gibbsOp_apply_eigenvector Hop β hv]
  exact (smul_assoc ((spectralTrace (gibbsOp Hop β))⁻¹ : ℝ)
    (Real.exp (-β * E) : ℂ) v).symm

/-- The entropy operator of the normalized Gibbs state has summable nonzero eigenvalues. -/
theorem gibbsState_entropyOp_hasSummableRealEigenvalues (Hop : Observable H) (β : ℝ)
    (hcompact : IsCompactOperator (gibbsOp Hop β))
    (hsummable : HasSummableRealEigenvalues (gibbsOp Hop β))
    (hZ : spectralTrace (gibbsOp Hop β) ≠ 0) :
    HasSummableRealEigenvalues (entropyOp (gibbsState Hop β hcompact hsummable hZ)) := by
  letI := finiteDimensional_of_gibbsOp_isCompact Hop β hcompact
  exact (gibbsState Hop β hcompact hsummable hZ).entropyOp_hasSummableRealEigenvalues

end QuantumTheory
