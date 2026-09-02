import LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalFormula
import LeanCondensedMatter.QuantumTheory.Entropy.Basic

/-!
# Entropy of diagonal density operators

Entropy-specific Hilbert-basis formulas for diagonal density states. General diagonal-state
normalization, basis-action, and expectation formulas are owned by
`QuantumTheory.DensityOperator.DiagonalFormula`.
-/

noncomputable section

namespace QuantumTheory

open ContinuousLinearMap

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The entropy-operator trace is the sum of `-wᵢ log wᵢ` in a diagonal presentation. -/
theorem entropyOpSpectralTraceClass_hasSum_diagonal (ρ : DensityOperator H)
    (b : HilbertBasis ι ℂ H) (w : ι → ℝ)
    (happly : ∀ i, ρ.op (b i) = (w i : ℂ) • b i)
    (hsummable : HasSummableRealEigenvalues (entropyOp ρ)) :
    HasSum (fun i => Real.negMulLog (w i))
      (entropyOpSpectralTraceClass ρ hsummable).trace := by
  have hsum := (entropyOpSpectralTraceClass ρ hsummable).hasSum_diagonalExpectationValue b
  exact HasSum.congr_fun hsum fun i => by
    apply Complex.ofReal_injective
    rw [coe_diagonalExpectationValue_right,
      entropyOp_apply_eigenvector ρ (by simpa using happly i),
      inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
    simp

/-- Spectral trace form of `entropyOpSpectralTraceClass_hasSum_diagonal`. -/
theorem entropyOpSpectralTraceClass_trace_eq_tsum_diagonal (ρ : DensityOperator H)
    (b : HilbertBasis ι ℂ H) (w : ι → ℝ)
    (happly : ∀ i, ρ.op (b i) = (w i : ℂ) • b i)
    (hsummable : HasSummableRealEigenvalues (entropyOp ρ)) :
    (entropyOpSpectralTraceClass ρ hsummable).trace =
      ∑' i, Real.negMulLog (w i) :=
  (entropyOpSpectralTraceClass_hasSum_diagonal ρ b w happly hsummable).tsum_eq.symm

/-- Entropy trace formula specialized to `diagonalDensityOperator`. -/
theorem entropyOpSpectralTraceClass_trace_diagonalDensityOperator
    (b : HilbertBasis ι ℂ H) (a : ι → ℝ)
    (ha : Summable fun i => ‖a i‖) (ha_nonneg : ∀ i, 0 ≤ a i)
    (hZ : 0 < ∑' i, a i)
    (hsummable : HasSummableRealEigenvalues
      (entropyOp (diagonalDensityOperator b a ha ha_nonneg hZ))) :
    (entropyOpSpectralTraceClass (diagonalDensityOperator b a ha ha_nonneg hZ)
      hsummable).trace =
      ∑' i, Real.negMulLog (normalizedDiagonalWeight a i) :=
  entropyOpSpectralTraceClass_trace_eq_tsum_diagonal
    (diagonalDensityOperator b a ha ha_nonneg hZ) b (normalizedDiagonalWeight a)
    (diagonalDensityOperator_apply_basis b a ha ha_nonneg hZ) hsummable

end QuantumTheory
