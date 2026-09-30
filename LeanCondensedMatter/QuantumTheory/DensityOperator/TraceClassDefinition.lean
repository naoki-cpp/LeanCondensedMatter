import LeanCondensedMatter.QuantumTheory.DensityOperator.Basic
import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.TraceClass.Banach
import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.TraceClass.GeneralIdeal

set_option linter.style.header false

/-!
# Trace-class definition of density operators

This file prototypes the representation-independent mixed-state definition using PhyslibAlpha's
general trace-class ideal:

```text
ρ ≥ 0,  ρ ∈ 𝒮₁(H),  Tr ρ = 1.
```

Unlike the existing spectral density-operator structure, compactness and spectral summability are
not stored as fields. They should eventually be derived from trace-classness.
-/

noncomputable section

namespace QuantumTheory

open scoped ComplexOrder
open ContinuousLinearMap
open ProbabilisticTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A density operator defined by positivity, trace-classness, and unit trace. -/
structure TraceClassDensityOperator (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The bounded operator representing the mixed state. -/
  op : H →L[ℂ] H
  /-- Positivity of the density operator. -/
  nonneg : 0 ≤ op
  /-- The density operator belongs to the trace-class ideal. -/
  traceClass : IsTraceClass op
  /-- Normalization by the basis-independent trace. -/
  trace_eq_one : trace op traceClass = 1

/-- Trace-class density operators are determined by their underlying bounded operators. -/
@[ext]
theorem TraceClassDensityOperator.ext {ρ σ : TraceClassDensityOperator H}
    (h : ρ.op = σ.op) : ρ = σ := by
  cases ρ
  cases σ
  cases h
  rfl

/-- Positivity in the existing continuous-linear-map API. -/
theorem TraceClassDensityOperator.isPositive (ρ : TraceClassDensityOperator H) :
    ρ.op.IsPositive :=
  ContinuousLinearMap.nonneg_iff_isPositive.mp ρ.nonneg

/-- A trace-class density operator is self-adjoint by positivity. -/
theorem TraceClassDensityOperator.isSelfAdjoint (ρ : TraceClassDensityOperator H) :
    IsSelfAdjoint ρ.op :=
  ρ.isPositive.isSelfAdjoint

/-- Bundle the underlying operator in PhyslibAlpha's trace-class Banach space. -/
def TraceClassDensityOperator.toTraceClass (ρ : TraceClassDensityOperator H) :
    TraceClass H :=
  TraceClass.ofOperator ρ.op ρ.traceClass

@[simp]
theorem TraceClassDensityOperator.toTraceClass_coe (ρ : TraceClassDensityOperator H) :
    ρ.toTraceClass.1 = ρ.op :=
  rfl

/-- The existing spectral density operator is trace class in PhyslibAlpha's general sense. -/
theorem DensityOperator.isTraceClass (ρ : DensityOperator H) :
    IsTraceClass ρ.op := by
  let hnonneg : 0 ≤ ρ.op :=
    ContinuousLinearMap.nonneg_iff_isPositive.mpr ρ.pos
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  refine ⟨w, b, ?_⟩
  have hsum :
      Summable (fun i : w =>
        diagonalExpectationValue ρ.op ρ.isSelfAdjoint (b i)) :=
    (ρ.hasSum_diagonalExpectationValue_eq_one b).summable
  have habs : CFC.abs ρ.op = ρ.op :=
    CFC.abs_of_nonneg ρ.op hnonneg
  apply hsum.congr
  intro i
  rw [habs]
  have h := congrArg Complex.re
    (coe_diagonalExpectationValue_right ρ.op ρ.isSelfAdjoint (b i))
  simpa using h

/-- Every existing spectral density operator determines a trace-class density operator. -/
noncomputable def DensityOperator.toTraceClassDensityOperator (ρ : DensityOperator H) :
    TraceClassDensityOperator H where
  op := ρ.op
  nonneg := ContinuousLinearMap.nonneg_iff_isPositive.mpr ρ.pos
  traceClass := ρ.isTraceClass
  trace_eq_one := by
    obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
    rw [trace_eq_of_hilbertBasis_of_nonneg
      (ContinuousLinearMap.nonneg_iff_isPositive.mpr ρ.pos) ρ.isTraceClass b]
    have hreal := ρ.hasSum_diagonalExpectationValue_eq_one b
    have hcomplex :
        HasSum
          (fun i : w =>
            ((diagonalExpectationValue ρ.op ρ.isSelfAdjoint (b i) : ℝ) : ℂ))
          1 := by
      simpa using Complex.ofRealCLM.hasSum hreal
    have hinner :
        HasSum (fun i : w => inner ℂ (b i) (ρ.op (b i))) 1 := by
      refine hcomplex.congr ?_
      intro i
      exact coe_diagonalExpectationValue_right ρ.op ρ.isSelfAdjoint (b i)
    exact hinner.tsum_eq

@[simp]
theorem DensityOperator.toTraceClassDensityOperator_op (ρ : DensityOperator H) :
    ρ.toTraceClassDensityOperator.op = ρ.op :=
  rfl

end QuantumTheory
