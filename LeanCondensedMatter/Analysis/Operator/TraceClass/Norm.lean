import LeanCondensedMatter.Analysis.Operator.TraceClass.General
import LeanCondensedMatter.Analysis.Operator.HilbertSchmidt.Norm

set_option linter.style.header false

/-!
# Trace norm

This module owns the canonical real trace norm for general trace-class bounded operators.
Its Hilbert-basis diagonal formula is derived directly from the Hilbert--Schmidt norm-square
representation of `sqrt(|T|)`.
-/

noncomputable section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace IsTraceClass

/-- The trace norm of a trace-class operator. -/
noncomputable def traceNorm {T : H →L[ℂ] H} (hT : IsTraceClass T) : ℝ :=
  IsHilbertSchmidt.normSq hT

/-- The trace norm is the diagonal series of `|T|` in every Hilbert basis. -/
theorem traceNorm_eq_tsum_diagonalExpectationValue {T : H →L[ℂ] H}
    (hT : IsTraceClass T) {ι : Type*} (d : HilbertBasis ι ℂ H) :
    hT.traceNorm =
      ∑' i, diagonalExpectationValue (CFC.abs T) (CFC.abs_nonneg T).isSelfAdjoint (d i) := by
  unfold traceNorm
  rw [IsHilbertSchmidt.normSq_eq_seriesWrt hT d]
  unfold hilbertSchmidtNormSqSeriesWrt
  apply tsum_congr
  intro i
  exact (diagonalExpectationValue_abs_eq_norm_sq_sqrt_abs T (d i)).symm

/-- The trace norm is independent of the proof of trace-class membership. -/
theorem traceNorm_proof_irrel {T : H →L[ℂ] H} (hT hT' : IsTraceClass T) :
    hT.traceNorm = hT'.traceNorm := by
  exact IsHilbertSchmidt.normSq_proof_irrel hT hT'

/-- The trace norm is nonnegative. -/
theorem traceNorm_nonneg {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    0 ≤ hT.traceNorm :=
  IsHilbertSchmidt.normSq_nonneg hT

/-- For a positive trace-class operator, the diagonal expectation values in every Hilbert basis
sum to the trace norm. -/
theorem hasSum_diagonalExpectationValue_eq_traceNorm {T : H →L[ℂ] H}
    (hT : IsTraceClass T) (hpos : T.IsPositive) {ι : Type*} (d : HilbertBasis ι ℂ H) :
    HasSum (fun i => diagonalExpectationValue T hpos.isSelfAdjoint (d i)) hT.traceNorm := by
  have hnonneg : 0 ≤ T := nonneg_iff_isPositive.mpr hpos
  have habs : CFC.abs T = T := CFC.abs_of_nonneg T hnonneg
  have hsummable :
      Summable (fun i => diagonalExpectationValue T hpos.isSelfAdjoint (d i)) := by
    simpa [IsTraceClassWrt, habs] using hT.isTraceClassWrt d
  have hnorm :
      hT.traceNorm = ∑' i, diagonalExpectationValue T hpos.isSelfAdjoint (d i) := by
    simpa [habs] using hT.traceNorm_eq_tsum_diagonalExpectationValue d
  rw [hnorm]
  exact hsummable.hasSum

/-- For a positive trace-class operator, the diagonal sum over any orthonormal family is bounded
by the trace norm. -/
theorem sum_diagonalExpectationValue_le_traceNorm {T : H →L[ℂ] H}
    (hT : IsTraceClass T) (hpos : T.IsPositive) {ι : Type*} {d : ι → H}
    (hd : Orthonormal ℂ d) :
    Summable (fun i => diagonalExpectationValue T hpos.isSelfAdjoint (d i)) ∧
      ∑' i, diagonalExpectationValue T hpos.isSelfAdjoint (d i) ≤ hT.traceNorm := by
  obtain ⟨w, b, hsub, hb_eq⟩ := hd.toSubtypeRange.exists_hilbertBasis_extension
  set g : w → ℝ := fun j =>
    diagonalExpectationValue T hpos.isSelfAdjoint (b j) with hg_def
  have htr : HasSum g hT.traceNorm := by
    simpa [g] using hT.hasSum_diagonalExpectationValue_eq_traceNorm hpos b
  have hgsum : Summable g := htr.summable
  have hgnonneg : ∀ j : w, 0 ≤ g j := fun j => by
    simpa [g] using diagonalExpectationValue_nonneg T hpos (b j)
  have hd_inj : Function.Injective d := hd.linearIndependent.injective
  set e : ι → w := fun i => ⟨d i, hsub ⟨i, rfl⟩⟩ with he_def
  have he_inj : Function.Injective e := fun i j hij => hd_inj (congrArg Subtype.val hij)
  have hge : ∀ i, g (e i) = diagonalExpectationValue T hpos.isSelfAdjoint (d i) := fun i => by
    change diagonalExpectationValue T hpos.isSelfAdjoint (b (e i)) = _
    rw [show (b (e i) : H) = d i from by rw [hb_eq]]
  have hfsum : Summable (fun i => g (e i)) := hgsum.comp_injective he_inj
  have hle : ∑' i, g (e i) ≤ hT.traceNorm :=
    hasSum_le_inj e he_inj (fun j _ => hgnonneg j) (fun _ => le_rfl) hfsum.hasSum htr
  refine ⟨hfsum.congr hge, ?_⟩
  rwa [tsum_congr hge] at hle

end IsTraceClass

end ContinuousLinearMap
