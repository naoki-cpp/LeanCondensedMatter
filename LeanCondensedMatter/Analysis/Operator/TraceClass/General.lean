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
    calc
      inner ℂ x (S (S x)) =
          inner ℂ x ((ContinuousLinearMap.adjoint S) (S x)) := by rw [hS.adjoint_eq]
      _ = inner ℂ (S x) (S x) := ContinuousLinearMap.adjoint_inner_right S x (S x)
  rw [hinner, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- Trace-class membership with respect to a basis is equivalent to the Hilbert--Schmidt property
of `sqrt(|T|)` with respect to that basis. -/
private theorem isTraceClassWrt_iff_isHilbertSchmidtWrt_sqrt_abs
    {ι : Type*} (d : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) :
    IsTraceClassWrt d T ↔
      IsHilbertSchmidtWrt d (CFC.sqrt (CFC.abs T)) := by
  unfold IsTraceClassWrt IsHilbertSchmidtWrt
  simpa only [diagonalExpectationValue_abs_eq_norm_sq_sqrt_abs]

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

end ContinuousLinearMap
