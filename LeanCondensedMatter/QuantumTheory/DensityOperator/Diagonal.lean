import LeanCondensedMatter.Analysis.Operator.TraceClass.DiagonalSpectralTrace
import LeanCondensedMatter.QuantumTheory.DensityOperator.Basic

/-!
# Diagonal density operators

Constructs a density operator from a Hilbert basis and summable nonnegative weights.
-/

noncomputable section

namespace QuantumTheory

open ContinuousLinearMap

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Normalize summable nonnegative diagonal weights to obtain a density operator. -/
def diagonalDensityOperator (b : HilbertBasis ι ℂ H) (a : ι → ℝ)
    (ha : Summable fun i => ‖a i‖) (ha_nonneg : ∀ i, 0 ≤ a i)
    (hZ : 0 < ∑' i, a i) : DensityOperator H := by
  let Z : ℝ := ∑' i, a i
  let p : ι → ℝ := fun i => Z⁻¹ * a i
  have hZ_pos : 0 < Z := by simpa [Z] using hZ
  have hZ_ne : Z ≠ 0 := ne_of_gt hZ_pos
  have hp_nonneg : ∀ i, 0 ≤ p i := by
    intro i
    exact mul_nonneg (inv_nonneg.mpr hZ_pos.le) (ha_nonneg i)
  have hp_norm : Summable fun i => ‖p i‖ := by
    have hscaled := ha.mul_left ‖Z⁻¹‖
    simpa [p, norm_mul] using hscaled
  refine
    { op := HilbertBasis.diagonalOp b (fun i => (p i : ℂ)) (by simpa using hp_norm)
      pos := HilbertBasis.diagonalOp_isPositive b p hp_norm hp_nonneg
      spectralTraceClass := HilbertBasis.diagonalOpSpectralTraceClass b p hp_norm hp_nonneg
      spectralTrace_eq_one := ?_ }
  calc
    (HilbertBasis.diagonalOpSpectralTraceClass b p hp_norm hp_nonneg).trace
        = ∑' i, p i :=
      HilbertBasis.diagonalOpSpectralTraceClass_trace b p hp_norm hp_nonneg
    _ = Z⁻¹ * ∑' i, a i := by
      simp only [p]
      rw [tsum_mul_left]
    _ = 1 := by
      change Z⁻¹ * Z = 1
      exact inv_mul_cancel₀ hZ_ne

end QuantumTheory
