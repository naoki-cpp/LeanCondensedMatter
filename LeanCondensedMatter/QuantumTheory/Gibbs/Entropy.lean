import LeanCondensedMatter.QuantumTheory.Gibbs.FreeEnergy
import LeanCondensedMatter.QuantumTheory.DensityOperator.Finite

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

/-- In finite dimensions, `Tr(ρH)` is exactly the complex embedding of the real energy value. -/
theorem linearMap_trace_mul_observable_eq_energyExpValue [FiniteDimensional ℂ H]
    (ρ : DensityOperator H) (Hop : Observable H) :
    LinearMap.trace ℂ H ((ρ.op ∘L Hop.1 : H →L[ℂ] H) : H →ₗ[ℂ] H) =
      (energyExpValue ρ Hop : ℂ) := by
  calc
    LinearMap.trace ℂ H ((ρ.op ∘L Hop.1 : H →L[ℂ] H) : H →ₗ[ℂ] H) =
        ρ.expectation Hop.1 := (ρ.expectation_eq_linearMap_trace Hop.1).symm
    _ = (energyExpValue ρ Hop : ℂ) := ρ.expectation_observable Hop

/-- The entropy operator of the normalized Gibbs state has summable nonzero eigenvalues. -/
theorem gibbsState_entropyOp_hasSummableRealEigenvalues (Hop : Observable H) (β : ℝ)
    (hcompact : IsCompactOperator (gibbsOp Hop β))
    (hsummable : HasSummableRealEigenvalues (gibbsOp Hop β))
    (hZ : spectralTrace (gibbsOp Hop β) ≠ 0) :
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

end QuantumTheory
