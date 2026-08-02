import LeanCondensedMatter.QuantumTheory.DiagonalDensityOperatorTraceClass
import LeanCondensedMatter.QuantumTheory.EntropyTraceClass

/-!
# Generic lemmas for density operators diagonal in a Hilbert basis

These results separate reusable Hilbert-basis calculations from Gibbs-specific proofs.  A density
operator that acts diagonally on a Hilbert basis has weights summing to one, and the spectral trace
of its entropy operator is the corresponding sum of `-p log p` whenever that entropy operator is
spectrally trace-class.
-/

noncomputable section

namespace QuantumTheory.TraceClass

open ContinuousLinearMap

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- If a density operator acts diagonally on a Hilbert basis, its diagonal weights sum to one. -/
theorem DensityOperator.hasSum_diagonal_weights (ρ : DensityOperator H)
    (b : HilbertBasis ι ℂ H) (w : ι → ℝ)
    (happly : ∀ i, ρ.op (b i) = (w i : ℂ) • b i) :
    HasSum w 1 := by
  have hsum := ρ.hasSum_inner_apply_eq_one b
  have hpoint :
      (fun i => (inner ℂ (b i) (ρ.op (b i)) : ℂ).re) = w := by
    funext i
    rw [happly i, inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
    simp
  rwa [hpoint] at hsum

/-- The diagonal weights of a density operator are summable. -/
theorem DensityOperator.summable_diagonal_weights (ρ : DensityOperator H)
    (b : HilbertBasis ι ℂ H) (w : ι → ℝ)
    (happly : ∀ i, ρ.op (b i) = (w i : ℂ) • b i) :
    Summable w :=
  (ρ.hasSum_diagonal_weights b w happly).summable

/-- A nonnegative diagonal weight of a density operator is at most one. -/
theorem DensityOperator.diagonal_weight_le_one (ρ : DensityOperator H)
    (b : HilbertBasis ι ℂ H) (w : ι → ℝ)
    (happly : ∀ i, ρ.op (b i) = (w i : ℂ) • b i)
    (hw_nonneg : ∀ i, 0 ≤ w i) (i : ι) :
    w i ≤ 1 := by
  have hs := ρ.summable_diagonal_weights b w happly
  calc
    w i ≤ ∑' j, w j := hs.le_tsum i (fun j _ => hw_nonneg j)
    _ = 1 := (ρ.hasSum_diagonal_weights b w happly).tsum_eq

/-- If `ρ` is diagonal with weights `w` in a Hilbert basis, then the entropy-operator trace is the
sum of `-wᵢ log wᵢ` in that same presentation. -/
theorem entropyOpSpectralTraceClass_hasSum_diagonal (ρ : DensityOperator H)
    (b : HilbertBasis ι ℂ H) (w : ι → ℝ)
    (happly : ∀ i, ρ.op (b i) = (w i : ℂ) • b i)
    (hsummable : HasSummableRealEigenvalues (entropyOp ρ)) :
    HasSum (fun i => Real.negMulLog (w i))
      (entropyOpSpectralTraceClass ρ hsummable).trace := by
  have hsum := (entropyOpSpectralTraceClass ρ hsummable).hasSum_inner_apply b
  have hpoint :
      (fun i => (inner ℂ (b i) (entropyOp ρ (b i)) : ℂ).re) =
        fun i => Real.negMulLog (w i) := by
    funext i
    rw [entropyOp_apply_eigenvector ρ (by simpa using happly i),
      inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
    simp
  rwa [hpoint] at hsum

/-- Spectral trace form of `entropyOpSpectralTraceClass_hasSum_diagonal`. -/
theorem entropyOpSpectralTraceClass_trace_eq_tsum_diagonal (ρ : DensityOperator H)
    (b : HilbertBasis ι ℂ H) (w : ι → ℝ)
    (happly : ∀ i, ρ.op (b i) = (w i : ℂ) • b i)
    (hsummable : HasSummableRealEigenvalues (entropyOp ρ)) :
    (entropyOpSpectralTraceClass ρ hsummable).trace =
      ∑' i, Real.negMulLog (w i) :=
  (entropyOpSpectralTraceClass_hasSum_diagonal ρ b w happly hsummable).tsum_eq.symm

end QuantumTheory.TraceClass
