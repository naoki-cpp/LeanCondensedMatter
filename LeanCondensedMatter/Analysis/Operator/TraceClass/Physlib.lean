import LeanCondensedMatter.Analysis.Operator.TraceClass.Bundled
import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.TraceClass.Basic

set_option linter.style.header false

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-!
# Physlib trace-class interface

The spectral trace-class bundle records compactness, symmetry, and eigenvalue summability for
LCM's spectral arguments. This module connects positive members of that bundle to Physlib's
general trace-class predicate and trace.
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ContinuousLinearMap
namespace SpectralTraceClass

variable {T : H →L[ℂ] H}

/-- A positive spectral-trace-class operator satisfies PhyslibAlpha's `IsTraceClass` criterion. -/
theorem toPhyslibIsTraceClass (h : SpectralTraceClass T) (hpos : T.IsPositive) :
    ProbabilisticTheory.IsTraceClass T := by
  classical
  have hT_nonneg : 0 ≤ T := T.nonneg_iff_isPositive.mpr hpos
  obtain ⟨w, b, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  refine ⟨w, b, ?_⟩
  apply (h.hasSum_diagonalExpectationValue b).summable.congr
  intro i
  rw [CFC.abs_of_nonneg T hT_nonneg]
  simpa using congrArg Complex.re
    (coe_diagonalExpectationValue_right T h.isSelfAdjoint (b i))

/-- Physlib's complex trace of a positive spectral-trace-class operator is the complex embedding
of its spectral trace. -/
theorem physlib_trace_eq_trace (h : SpectralTraceClass T) (hpos : T.IsPositive) :
    ProbabilisticTheory.trace T (h.toPhyslibIsTraceClass hpos) = (h.trace : ℂ) := by
  classical
  have hT_nonneg : 0 ≤ T := T.nonneg_iff_isPositive.mpr hpos
  obtain ⟨w, b, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  have hsum := h.hasSum_diagonalExpectationValue b
  calc
    _ = ∑' i : w, inner ℂ (b i) (T (b i)) := by
      rw [ProbabilisticTheory.trace_eq_of_hilbertBasis_of_nonneg hT_nonneg
        (h.toPhyslibIsTraceClass hpos) b]
    _ = ∑' i : w, (diagonalExpectationValue T h.isSelfAdjoint (b i) : ℂ) := by
      apply tsum_congr
      intro i
      exact (coe_diagonalExpectationValue_right T h.isSelfAdjoint (b i)).symm
    _ = h.trace := by
      rw [← Complex.ofReal_tsum
        (fun i : w => diagonalExpectationValue T h.isSelfAdjoint (b i))]
      exact congrArg Complex.ofReal hsum.tsum_eq

/-- Convert a normalized spectral trace into Physlib's complex trace normalization. -/
theorem physlib_trace_eq_one_of_trace_eq_one (h : SpectralTraceClass T)
    (hpos : T.IsPositive) (htrace : h.trace = 1) :
    ProbabilisticTheory.trace T (h.toPhyslibIsTraceClass hpos) = 1 := by
  rw [h.physlib_trace_eq_trace hpos]
  exact congrArg Complex.ofReal htrace

end SpectralTraceClass
end ContinuousLinearMap
