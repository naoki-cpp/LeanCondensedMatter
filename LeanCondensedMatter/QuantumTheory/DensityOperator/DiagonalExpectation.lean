import LeanCondensedMatter.Analysis.FunctionalCalculus.CFC
import LeanCondensedMatter.Analysis.Operator.TraceClass.Cyclicity
import LeanCondensedMatter.QuantumTheory.DensityOperator.ObservableExpectation

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-!
# Countable diagonal expectation formulas

The positive square root of a density operator is Hilbert–Schmidt. This identifies the canonical
spectral expectation with the Hilbert–Schmidt pairing `⟪√ρ, A√ρ⟫`, whose basis independence yields
countable Hilbert-basis formulas and absolute convergence without a finite-dimensional hypothesis.
-/

noncomputable section

namespace QuantumTheory

open ContinuousLinearMap

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The positive square root of a density operator. -/
noncomputable def DensityOperator.sqrtOp (ρ : DensityOperator H) : H →L[ℂ] H :=
  cfc Real.sqrt ρ.op

/-- The square-root density operator acts on an eigenvector by the square root of its eigenvalue. -/
theorem DensityOperator.sqrtOp_apply_eigenvector (ρ : DensityOperator H) {v : H} {c : ℝ}
    (hv : (ρ.op : H →ₗ[ℂ] H) v = (c : ℂ) • v) :
    ρ.sqrtOp v = (Real.sqrt c : ℂ) • v := by
  simpa [DensityOperator.sqrtOp] using
    (cfc_apply_eigenvector (T := ρ.op) ρ.pos.isSelfAdjoint hv
      (f := Real.sqrt) Real.continuous_sqrt)

/-- The density-operator square root agrees with the canonical positive operator square root. -/
theorem DensityOperator.sqrtOp_eq_cfcSqrt (ρ : DensityOperator H) :
    ρ.sqrtOp = CFC.sqrt ρ.op := by
  have hnonneg : 0 ≤ ρ.op := nonneg_iff_isPositive.mpr ρ.pos
  rw [CFC.sqrt_eq_real_sqrt ρ.op hnonneg, cfcₙ_eq_cfc]
  rfl

/-- The positive square root of a density operator is self-adjoint. -/
theorem DensityOperator.sqrtOp_isSelfAdjoint (ρ : DensityOperator H) :
    IsSelfAdjoint ρ.sqrtOp := by
  rw [ρ.sqrtOp_eq_cfcSqrt]
  exact (CFC.sqrt_nonneg ρ.op).isSelfAdjoint

/-- The square of the positive square root recovers the density operator. -/
theorem DensityOperator.sqrtOp_mul_self (ρ : DensityOperator H) :
    ρ.sqrtOp * ρ.sqrtOp = ρ.op := by
  have hnonneg : 0 ≤ ρ.op := nonneg_iff_isPositive.mpr ρ.pos
  rw [ρ.sqrtOp_eq_cfcSqrt]
  exact CFC.sqrt_mul_sqrt_self ρ.op hnonneg

/-- The positive square root of a density operator is Hilbert–Schmidt.
This is the positive specialization of general trace-class membership. -/
theorem DensityOperator.sqrtOp_isHilbertSchmidt (ρ : DensityOperator H) :
    IsHilbertSchmidt ρ.sqrtOp := by
  have hnonneg : 0 ≤ ρ.op := nonneg_iff_isPositive.mpr ρ.pos
  have habs : CFC.abs ρ.op = ρ.op := CFC.abs_of_nonneg ρ.op hnonneg
  rw [ρ.sqrtOp_eq_cfcSqrt]
  simpa [IsTraceClass, habs] using ρ.isTraceClass

/-- The canonical density-state expectation is the basis-independent Hilbert–Schmidt pairing
`⟪√ρ, A√ρ⟫`. This formula is valid for every bounded operator, not only observables. -/
theorem DensityOperator.expectation_eq_innerHS (ρ : DensityOperator H)
    (A : H →L[ℂ] H) (d : HilbertBasis ι ℂ H) :
    ρ.expectation A = innerHS d ρ.sqrtOp (A * ρ.sqrtOp) := by
  let hsqrt : IsHilbertSchmidt ρ.sqrtOp := ρ.sqrtOp_isHilbertSchmidt
  let hsqrtA : IsHilbertSchmidt (ρ.sqrtOp * A) :=
    isHilbertSchmidt_comp_right hsqrt A
  let hleft : IsTraceClass (ρ.sqrtOp * (ρ.sqrtOp * A)) :=
    hsqrt.mul_isTraceClass hsqrtA
  let hright : IsTraceClass ((ρ.sqrtOp * A) * ρ.sqrtOp) :=
    hsqrtA.mul_isTraceClass hsqrt
  have hleftOp : ρ.sqrtOp * (ρ.sqrtOp * A) = ρ.op * A := by
    rw [← mul_assoc, ρ.sqrtOp_mul_self]
  have hfactorRight :
      ContinuousLinearMap.adjoint ρ.sqrtOp * (A * ρ.sqrtOp) =
        (ρ.sqrtOp * A) * ρ.sqrtOp := by
    rw [ρ.sqrtOp_isSelfAdjoint.adjoint_eq, ← mul_assoc]
  have htraceLeft :
      (ρ.isTraceClass.comp_right A).trace = hleft.trace := by
    rw [(ρ.isTraceClass.comp_right A).trace_eq_seriesWrt d,
      hleft.trace_eq_seriesWrt d]
    unfold traceSeriesWrt
    apply tsum_congr
    intro i
    rw [hleftOp]
  calc
    ρ.expectation A = (ρ.isTraceClass.comp_right A).trace := ρ.expectation_apply A
    _ = hleft.trace := htraceLeft
    _ = hright.trace := by
      exact IsHilbertSchmidt.trace_mul_comm hsqrt hsqrtA
    _ = innerHS d ρ.sqrtOp (A * ρ.sqrtOp) :=
      hright.trace_eq_innerHS_of_factorization hfactorRight d

end QuantumTheory
