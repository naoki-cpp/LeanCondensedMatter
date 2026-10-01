import LeanCondensedMatter.Analysis.Operator.DiagonalExpectation
import LeanCondensedMatter.Analysis.Operator.HilbertSchmidt.Basic
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
    change inner ℂ x (S (S x)) = inner ℂ (S x) (S x)
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

/-- A bounded operator is trace class if the diagonal series of `|T|` is summable in one
Hilbert basis. -/
def IsTraceClass (T : H →L[ℂ] H) : Prop :=
  ∃ (w : Set H) (d : HilbertBasis w ℂ H), IsTraceClassWrt d T

/-- Trace-class membership can be checked in any chosen Hilbert basis. -/
theorem isTraceClass_iff_isTraceClassWrt {ι : Type*} (d : HilbertBasis ι ℂ H)
    (T : H →L[ℂ] H) :
    IsTraceClass T ↔ IsTraceClassWrt d T := by
  constructor
  · rintro ⟨w, b, hb⟩
    exact (isTraceClassWrt_iff b d T).mp hb
  · intro hd
    obtain ⟨w, b, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
    exact ⟨w, b, (isTraceClassWrt_iff d b T).mp hd⟩

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

/-- The trace-norm series evaluated in a chosen Hilbert basis. Basis independence is proved below
under trace-class membership. -/
noncomputable def traceNormWrt {ι : Type*} (d : HilbertBasis ι ℂ H)
    (T : H →L[ℂ] H) : ℝ :=
  ∑' i, diagonalExpectationValue (CFC.abs T) (CFC.abs_nonneg T).isSelfAdjoint (d i)

/-- The basis-relative trace-norm series is the squared Hilbert--Schmidt norm series of
`sqrt(|T|)`. -/
theorem traceNormWrt_eq_tsum_norm_sq_sqrt_abs {ι : Type*}
    (d : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) :
    traceNormWrt d T = ∑' i, ‖CFC.sqrt (CFC.abs T) (d i)‖ ^ 2 := by
  unfold traceNormWrt
  apply tsum_congr
  intro i
  exact diagonalExpectationValue_abs_eq_norm_sq_sqrt_abs T (d i)

/-- The trace-norm series has the same value in every Hilbert basis for a trace-class operator. -/
theorem traceNormWrt_eq {ι κ : Type*} (d : HilbertBasis ι ℂ H)
    (f : HilbertBasis κ ℂ H) (T : H →L[ℂ] H) (hT : IsTraceClass T) :
    traceNormWrt d T = traceNormWrt f T := by
  have hd : IsTraceClassWrt d T := hT.isTraceClassWrt d
  have hHS :
      IsHilbertSchmidtWrt d (CFC.sqrt (CFC.abs T)) :=
    (isTraceClassWrt_iff_isHilbertSchmidtWrt_sqrt_abs d T).mp hd
  rw [traceNormWrt_eq_tsum_norm_sq_sqrt_abs,
    traceNormWrt_eq_tsum_norm_sq_sqrt_abs]
  exact (summable_norm_sq_apply_and_tsum_eq d f (CFC.sqrt (CFC.abs T)) hHS).2.symm

end ContinuousLinearMap
