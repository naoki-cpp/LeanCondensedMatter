import LeanCondensedMatter.Analysis.Operator.TraceClass.Spectral.Diagonal
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

/-- Summable diagonal entropy weights make the entropy operator trace-class. -/
theorem DensityOperator.entropyOp_isTraceClass_of_diagonal
    (ρ : DensityOperator H) (b : HilbertBasis ι ℂ H) (w : ι → ℝ)
    (happly : ∀ i, ρ.op (b i) = (w i : ℂ) • b i)
    (hsum : Summable fun i => ‖Real.negMulLog (w i)‖) :
    IsTraceClass (entropyOp ρ) := by
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
  exact (HilbertBasis.diagonalOpSpectralTraceClass b a ha ha_nonneg).isTraceClass

/-- The entropy operator's lossless real trace is the sum of `-wᵢ log wᵢ` in a diagonal presentation. -/
theorem hasSum_entropyOp_diagonal (ρ : DensityOperator H)
    (b : HilbertBasis ι ℂ H) (w : ι → ℝ)
    (happly : ∀ i, ρ.op (b i) = (w i : ℂ) • b i)
    (htrace : IsTraceClass (entropyOp ρ)) :
    HasSum (fun i => Real.negMulLog (w i))
      (htrace.realTrace (entropyOp_isSelfAdjoint ρ)) := by
  have hsum := htrace.hasSum_realTrace (entropyOp_isSelfAdjoint ρ) b
  exact HasSum.congr_fun hsum fun i => by
    apply Complex.ofReal_injective
    rw [coe_diagonalExpectationValue_right,
      entropyOp_apply_eigenvector ρ (by simpa using happly i),
      inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
    simp

/-- A convergent diagonal Shannon-entropy series gives finite von Neumann entropy with
the same real value. Trace-classness of the entropy operator is derived internally. -/
theorem DensityOperator.vonNeumannEntropy_ne_top_and_toReal_eq_of_hasSum_diagonal
    (ρ : DensityOperator H) (b : HilbertBasis ι ℂ H) (w : ι → ℝ)
    (happly : ∀ i, ρ.op (b i) = (w i : ℂ) • b i) {S : ℝ}
    (hsum : HasSum (fun i => Real.negMulLog (w i)) S) :
    vonNeumannEntropy ρ ≠ ⊤ ∧ (vonNeumannEntropy ρ).toReal = S := by
  have htrace : IsTraceClass (entropyOp ρ) :=
    ρ.entropyOp_isTraceClass_of_diagonal b w happly hsum.summable.norm
  have hEntropySum := hasSum_entropyOp_diagonal ρ b w happly htrace
  have htrace_eq : htrace.realTrace (entropyOp_isSelfAdjoint ρ) = S :=
    hEntropySum.unique hsum
  have hw_nonneg : ∀ i, 0 ≤ w i := ρ.diagonal_weight_nonneg b w happly
  have hw_le_one : ∀ i, w i ≤ 1 :=
    ρ.diagonal_weight_le_one b w happly hw_nonneg
  have htrace_nonneg : 0 ≤ htrace.realTrace (entropyOp_isSelfAdjoint ρ) := by
    rw [← hEntropySum.tsum_eq]
    exact tsum_nonneg fun i => Real.negMulLog_nonneg (hw_nonneg i) (hw_le_one i)
  have hEntropyBridge := vonNeumannEntropy_eq_ofReal_entropyOp_realTrace ρ htrace
  constructor
  · rw [hEntropyBridge]
    exact ENNReal.ofReal_ne_top
  · rw [hEntropyBridge, ENNReal.toReal_ofReal htrace_nonneg, htrace_eq]

/-- Real-trace form of `hasSum_entropyOp_diagonal`. -/
theorem entropyOp_realTrace_eq_tsum_diagonal (ρ : DensityOperator H)
    (b : HilbertBasis ι ℂ H) (w : ι → ℝ)
    (happly : ∀ i, ρ.op (b i) = (w i : ℂ) • b i)
    (htrace : IsTraceClass (entropyOp ρ)) :
    htrace.realTrace (entropyOp_isSelfAdjoint ρ) =
      ∑' i, Real.negMulLog (w i) :=
  (hasSum_entropyOp_diagonal ρ b w happly htrace).tsum_eq.symm

end QuantumTheory
