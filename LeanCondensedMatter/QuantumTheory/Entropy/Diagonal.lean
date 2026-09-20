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

/-- Summable diagonal entropy weights make the entropy operator spectrally summable. -/
theorem DensityOperator.entropyOp_hasSummableRealEigenvalues_of_diagonal
    (ρ : DensityOperator H) (b : HilbertBasis ι ℂ H) (w : ι → ℝ)
    (happly : ∀ i, ρ.op (b i) = (w i : ℂ) • b i)
    (hsum : Summable fun i => ‖Real.negMulLog (w i)‖) :
    HasSummableRealEigenvalues (entropyOp ρ) := by
  let a : ι → ℝ := fun i => Real.negMulLog (w i)
  have hw_nonneg : ∀ i, 0 ≤ w i := ρ.diagonal_weight_nonneg b w happly
  have hw_le_one : ∀ i, w i ≤ 1 :=
    ρ.diagonal_weight_le_one b w happly hw_nonneg
  have ha_nonneg : ∀ i, 0 ≤ a i := fun i =>
    Real.negMulLog_nonneg (hw_nonneg i) (hw_le_one i)
  have ha : Summable fun i => ‖a i‖ := by
    simpa [a] using hsum
  have hac : Summable fun i => ‖(a i : ℂ)‖ := by
    simpa using ha
  have hop :
      entropyOp ρ = HilbertBasis.diagonalOp b (fun i => (a i : ℂ)) := by
    apply ContinuousLinearMap.ext_on
      (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span)
    rintro _ ⟨i, rfl⟩
    rw [entropyOp_apply_eigenvector ρ (by simpa using happly i)]
    rw [HilbertBasis.diagonalOp_apply_basis b (fun i => (a i : ℂ)) hac i]
  rw [hop]
  exact (HilbertBasis.diagonalOpSpectralTraceClass b a ha ha_nonneg).summable

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

end QuantumTheory
