import LeanCondensedMatter.Analysis.Operator.TraceClass.DiagonalSpectralTrace
import LeanCondensedMatter.QuantumTheory.DensityOperatorTraceClass

/-!
# Normalized diagonal density operators

Constructs a genuine infinite-dimensional density operator from a Hilbert basis and summable
nonnegative weights. If `Z = ∑' i, a i` is positive, the normalized weights `Z⁻¹ a i` define a
positive compact spectral-trace-class operator with trace one.

This is the bounded heat-operator backend needed by a future discrete unbounded Hamiltonian API:
the Hamiltonian itself need not be represented as a bounded continuous linear map; it can instead
provide an energy basis and summable Boltzmann weights.
-/

noncomputable section

namespace QuantumTheory.TraceClass

open ContinuousLinearMap

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Normalize summable nonnegative diagonal weights to obtain a trace-class density operator. -/
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

end QuantumTheory.TraceClass
