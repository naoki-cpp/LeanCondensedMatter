import LeanCondensedMatter.QuantumTheory.DensityOperator.Diagonal
import LeanCondensedMatter.QuantumTheory.Entropy.Basic

/-!
# Entropy of diagonal density operators

Reusable Hilbert-basis formulas for diagonal density states and their entropy operators.
-/

noncomputable section

namespace QuantumTheory

open ContinuousLinearMap

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- If a density operator is diagonal in a Hilbert basis, its weights sum to one. -/
theorem DensityOperator.hasSum_diagonal_weights (ρ : DensityOperator H)
    (b : HilbertBasis ι ℂ H) (w : ι → ℝ)
    (happly : ∀ i, ρ.op (b i) = (w i : ℂ) • b i) :
    HasSum w 1 := by
  have hsum := ρ.hasSum_diagonalExpectationValue_eq_one b
  have hpoint :
      (fun i => diagonalExpectationValue ρ.op ρ.isSelfAdjoint (b i)) = w := by
    funext i
    apply Complex.ofReal_injective
    rw [coe_diagonalExpectationValue_right, happly i, inner_smul_right,
      inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
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

/-- The entropy-operator trace is the sum of `-wᵢ log wᵢ` in a diagonal presentation. -/
theorem entropyOpSpectralTraceClass_hasSum_diagonal (ρ : DensityOperator H)
    (b : HilbertBasis ι ℂ H) (w : ι → ℝ)
    (happly : ∀ i, ρ.op (b i) = (w i : ℂ) • b i)
    (hsummable : HasSummableRealEigenvalues (entropyOp ρ)) :
    HasSum (fun i => Real.negMulLog (w i))
      (entropyOpSpectralTraceClass ρ hsummable).trace := by
  have hsum := (entropyOpSpectralTraceClass ρ hsummable).hasSum_diagonalExpectationValue b
  have hpoint :
      (fun i => diagonalExpectationValue (entropyOp ρ)
        (entropyOpSpectralTraceClass ρ hsummable).isSelfAdjoint (b i)) =
        fun i => Real.negMulLog (w i) := by
    funext i
    apply Complex.ofReal_injective
    rw [coe_diagonalExpectationValue_right,
      entropyOp_apply_eigenvector ρ (by simpa using happly i),
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

/-- The normalized weight used by `diagonalDensityOperator`. -/
def normalizedDiagonalWeight (a : ι → ℝ) (i : ι) : ℝ :=
  (∑' j, a j)⁻¹ * a i

/-- Absolute summability is preserved by normalization. -/
theorem summable_norm_normalizedDiagonalWeight (a : ι → ℝ)
    (ha : Summable fun i => ‖a i‖) :
    Summable fun i => ‖normalizedDiagonalWeight a i‖ := by
  have hscaled := ha.mul_left ‖(∑' j, a j)⁻¹‖
  simpa [normalizedDiagonalWeight, norm_mul] using hscaled

/-- The normalized diagonal density operator acts by its normalized weight. -/
theorem diagonalDensityOperator_apply_basis (b : HilbertBasis ι ℂ H) (a : ι → ℝ)
    (ha : Summable fun i => ‖a i‖) (ha_nonneg : ∀ i, 0 ≤ a i)
    (hZ : 0 < ∑' i, a i) (i : ι) :
    (diagonalDensityOperator b a ha ha_nonneg hZ).op (b i) =
      (normalizedDiagonalWeight a i : ℂ) • b i := by
  change HilbertBasis.diagonalOp b
      (fun i => (normalizedDiagonalWeight a i : ℂ)) (b i) = _
  simpa using HilbertBasis.diagonalOp_apply_basis b
    (fun i => (normalizedDiagonalWeight a i : ℂ))
    (by simpa using summable_norm_normalizedDiagonalWeight a ha) i

/-- Normalized nonnegative weights remain nonnegative. -/
theorem normalizedDiagonalWeight_nonneg (a : ι → ℝ) (ha_nonneg : ∀ i, 0 ≤ a i)
    (hZ : 0 < ∑' i, a i) (i : ι) :
    0 ≤ normalizedDiagonalWeight a i :=
  mul_nonneg (inv_nonneg.mpr hZ.le) (ha_nonneg i)

/-- The normalized diagonal weights sum to one. -/
theorem hasSum_normalizedDiagonalWeight (b : HilbertBasis ι ℂ H) (a : ι → ℝ)
    (ha : Summable fun i => ‖a i‖) (ha_nonneg : ∀ i, 0 ≤ a i)
    (hZ : 0 < ∑' i, a i) :
    HasSum (normalizedDiagonalWeight a) 1 :=
  (diagonalDensityOperator b a ha ha_nonneg hZ).hasSum_diagonal_weights b
    (normalizedDiagonalWeight a) (diagonalDensityOperator_apply_basis b a ha ha_nonneg hZ)

/-- Every normalized diagonal weight is at most one. -/
theorem normalizedDiagonalWeight_le_one (b : HilbertBasis ι ℂ H) (a : ι → ℝ)
    (ha : Summable fun i => ‖a i‖) (ha_nonneg : ∀ i, 0 ≤ a i)
    (hZ : 0 < ∑' i, a i) (i : ι) :
    normalizedDiagonalWeight a i ≤ 1 :=
  (diagonalDensityOperator b a ha ha_nonneg hZ).diagonal_weight_le_one b
    (normalizedDiagonalWeight a) (diagonalDensityOperator_apply_basis b a ha ha_nonneg hZ)
    (normalizedDiagonalWeight_nonneg a ha_nonneg hZ) i

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
