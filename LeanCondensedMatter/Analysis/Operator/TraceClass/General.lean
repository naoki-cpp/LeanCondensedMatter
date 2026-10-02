import LeanCondensedMatter.Analysis.Operator.DiagonalExpectation
import LeanCondensedMatter.Analysis.Operator.HilbertSchmidt.Norm
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs

set_option linter.style.header false

/-!
# General trace-class membership

This module defines trace-class membership for bounded operators on a complete complex Hilbert
space. For a Hilbert basis `d`, `IsTraceClassWrt d T` means that the nonnegative diagonal
series of the canonical operator absolute value `CFC.abs T = |T|` is summable.

Basis independence is reduced to the existing Hilbert--Schmidt basis-independence theorem by
identifying the diagonal of `|T|` with the squared basis norms of `CFC.sqrt (CFC.abs T)`.
-/

noncomputable section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Trace-class membership with respect to a Hilbert basis: the diagonal series of `|T|` is
summable. -/
def IsTraceClassWrt {ι : Type*} (d : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) : Prop :=
  Summable (fun i =>
    diagonalExpectationValue (CFC.abs T) (CFC.abs_nonneg T).isSelfAdjoint (d i))

/-- A diagonal matrix element of `|T|` is the squared norm of
`sqrt(|T|)` applied to the same vector. -/
theorem diagonalExpectationValue_abs_eq_norm_sq_sqrt_abs
    (T : H →L[ℂ] H) (x : H) :
    diagonalExpectationValue (CFC.abs T) (CFC.abs_nonneg T).isSelfAdjoint x =
      ‖CFC.sqrt (CFC.abs T) x‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [coe_diagonalExpectationValue_right]
  let S : H →L[ℂ] H := CFC.sqrt (CFC.abs T)
  have hS : IsSelfAdjoint S := (CFC.sqrt_nonneg (CFC.abs T)).isSelfAdjoint
  have hsq : S * S = CFC.abs T := by
    exact CFC.sqrt_mul_sqrt_self (CFC.abs T) (CFC.abs_nonneg T)
  have hinner : inner ℂ x ((CFC.abs T) x) = inner ℂ (S x) (S x) := by
    rw [← hsq, mul_apply_eq_comp]
    calc
      inner ℂ x (S (S x)) =
          inner ℂ x ((ContinuousLinearMap.adjoint S) (S x)) := by rw [hS.adjoint_eq]
      _ = inner ℂ (S x) (S x) := ContinuousLinearMap.adjoint_inner_right S x (S x)
  rw [hinner, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- Trace-class membership with respect to a basis is equivalent to the Hilbert--Schmidt property
of `sqrt(|T|)` with respect to that basis. -/
theorem isTraceClassWrt_iff_isHilbertSchmidtWrt_sqrt_abs
    {ι : Type*} (d : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) :
    IsTraceClassWrt d T ↔
      IsHilbertSchmidtWrt d (CFC.sqrt (CFC.abs T)) := by
  unfold IsTraceClassWrt IsHilbertSchmidtWrt
  simpa only [diagonalExpectationValue_abs_eq_norm_sq_sqrt_abs]

/-- `IsTraceClassWrt` is independent of the chosen Hilbert basis. -/
theorem isTraceClassWrt_iff {ι κ : Type*} (d : HilbertBasis ι ℂ H)
    (f : HilbertBasis κ ℂ H) (T : H →L[ℂ] H) :
    IsTraceClassWrt d T ↔ IsTraceClassWrt f T := by
  rw [isTraceClassWrt_iff_isHilbertSchmidtWrt_sqrt_abs,
    isTraceClassWrt_iff_isHilbertSchmidtWrt_sqrt_abs]
  exact isHilbertSchmidtWrt_iff d f (CFC.sqrt (CFC.abs T))

/-- A bounded operator is trace class when `sqrt(|T|)` is Hilbert--Schmidt. The equivalent
Hilbert-basis diagonal criterion is `isTraceClass_iff_isTraceClassWrt`. -/
def IsTraceClass (T : H →L[ℂ] H) : Prop :=
  IsHilbertSchmidt (CFC.sqrt (CFC.abs T))

/-- Trace-class membership is equivalent to summability of the diagonal of `|T|` in any chosen
Hilbert basis. -/
theorem isTraceClass_iff_isTraceClassWrt {ι : Type*} (d : HilbertBasis ι ℂ H)
    (T : H →L[ℂ] H) :
    IsTraceClass T ↔ IsTraceClassWrt d T := by
  unfold IsTraceClass
  rw [isTraceClassWrt_iff_isHilbertSchmidtWrt_sqrt_abs]
  exact isHilbertSchmidt_iff_isHilbertSchmidtWrt d (CFC.sqrt (CFC.abs T))

/-- A basis-independent trace-class witness supplies summability in every Hilbert basis. -/
theorem IsTraceClass.isTraceClassWrt {T : H →L[ℂ] H} (hT : IsTraceClass T)
    {ι : Type*} (d : HilbertBasis ι ℂ H) :
    IsTraceClassWrt d T :=
  (isTraceClass_iff_isTraceClassWrt d T).mp hT

/-- Evidence of trace-class membership in one Hilbert basis packages into the basis-independent
predicate. -/
theorem IsTraceClass.of_isTraceClassWrt {ι : Type*} {d : HilbertBasis ι ℂ H}
    {T : H →L[ℂ] H} (hT : IsTraceClassWrt d T) :
    IsTraceClass T :=
  (isTraceClass_iff_isTraceClassWrt d T).mpr hT

/-- The totalized trace-norm series evaluated in a chosen Hilbert basis. Outside trace-class
membership, this is only the totalized `tsum` value and is not the trace norm. -/
noncomputable def traceNormSeriesWrt {ι : Type*} (d : HilbertBasis ι ℂ H)
    (T : H →L[ℂ] H) : ℝ :=
  hilbertSchmidtNormSqSeriesWrt d (CFC.sqrt (CFC.abs T))

/-- For a trace-class operator, the trace-norm series has the same value in every Hilbert basis. -/
theorem traceNormSeriesWrt_eq {ι κ : Type*} (d : HilbertBasis ι ℂ H)
    (f : HilbertBasis κ ℂ H) (T : H →L[ℂ] H) (hT : IsTraceClass T) :
    traceNormSeriesWrt d T = traceNormSeriesWrt f T := by
  unfold traceNormSeriesWrt
  exact hilbertSchmidtNormSqSeriesWrt_eq d f (CFC.sqrt (CFC.abs T)) hT

namespace IsTraceClass

/-- The trace norm of a trace-class operator. -/
noncomputable def traceNorm {T : H →L[ℂ] H} (hT : IsTraceClass T) : ℝ :=
  IsHilbertSchmidt.normSq hT

/-- The trace norm is the diagonal trace-norm series in every Hilbert basis. -/
theorem traceNorm_eq_seriesWrt {T : H →L[ℂ] H} (hT : IsTraceClass T)
    {ι : Type*} (d : HilbertBasis ι ℂ H) :
    hT.traceNorm = traceNormSeriesWrt d T := by
  unfold traceNorm traceNormSeriesWrt
  exact IsHilbertSchmidt.normSq_eq_seriesWrt hT d

/-- The trace norm is independent of the proof of trace-class membership. -/
theorem traceNorm_proof_irrel {T : H →L[ℂ] H} (hT hT' : IsTraceClass T) :
    hT.traceNorm = hT'.traceNorm := by
  exact IsHilbertSchmidt.normSq_proof_irrel hT hT'

/-- The trace norm is nonnegative. -/
theorem traceNorm_nonneg {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    0 ≤ hT.traceNorm :=
  IsHilbertSchmidt.normSq_nonneg hT

end IsTraceClass

end ContinuousLinearMap
