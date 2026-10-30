import LeanCondensedMatter.Analysis.Operator.TraceClass.Trace
import LeanCondensedMatter.QuantumTheory.DensityOperator.ExpectationOrder
import LeanCondensedMatter.QuantumTheory.DensityOperator.PureState
import LeanCondensedMatter.QuantumTheory.Postulates
import Mathlib.LinearAlgebra.Complex.Module

/-!
# Real expectations of observables

The canonical density-state expectation remains complex-linear on arbitrary bounded operators.
When the operator is an observable, self-adjointness proves that scalar to be real, and this module
transports it losslessly to `ℝ`. It also identifies the density-state expectation of a rank-one pure
state with the vector-state expectation from `QuantumTheory.Postulates`.
-/

noncomputable section

namespace QuantumTheory

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The complex density-state expectation of an observable, bundled with its self-adjointness. -/
noncomputable def DensityOperator.observableExpectationSelfAdjoint
    (ρ : DensityOperator H) (A : Observable H) : selfAdjoint ℂ :=
  ⟨ρ.expectation A.1,
    ρ.expectation_isSelfAdjoint_of_isSymmetric A.2.isSymmetric⟩

/-- The real expectation value of an observable in a density state, obtained losslessly from the
proved-self-adjoint complex expectation rather than by projecting an arbitrary scalar with `.re`. -/
noncomputable def DensityOperator.observableExpectation
    (ρ : DensityOperator H) (A : Observable H) : ℝ :=
  Complex.selfAdjointEquiv (ρ.observableExpectationSelfAdjoint A)

/-- The canonical complex expectation is exactly the complex embedding of the real observable
expectation. -/
@[simp]
theorem DensityOperator.expectation_observable
    (ρ : DensityOperator H) (A : Observable H) :
    ρ.expectation A.1 = (ρ.observableExpectation A : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa [DensityOperator.observableExpectation,
      DensityOperator.observableExpectationSelfAdjoint, Complex.selfAdjointEquiv] using
      ρ.expectation_im_eq_zero_of_isSymmetric A.2.isSymmetric

/-- The complex expectation in the rank-one density operator of a pure state agrees with the
canonical vector-state expectation. -/
theorem DensityOperator.expectation_pure_observable
    (ψ : StateVector H) (A : Observable H) :
    (pure ψ).expectation A.1 = expValue A ψ := by
  have hproduct : (pure ψ).op * A.1 =
      InnerProductSpace.rankOne ℂ ψ.1 (ContinuousLinearMap.adjoint A.1 ψ.1) := by
    ext x
    change (inner ℂ ψ.1 (A.1 x)) • ψ.1 =
      (inner ℂ (ContinuousLinearMap.adjoint A.1 ψ.1) x) • ψ.1
    rw [ContinuousLinearMap.adjoint_inner_left]
  have htrace : IsTraceClass
      (InnerProductSpace.rankOne ℂ ψ.1 (ContinuousLinearMap.adjoint A.1 ψ.1)) := by
    rw [← hproduct]
    exact (pure ψ).isTraceClass.comp_right A.1
  rw [DensityOperator.expectation_apply,
    IsTraceClass.trace_congr ((pure ψ).isTraceClass.comp_right A.1) htrace hproduct,
    htrace.trace_rankOne]
  exact ContinuousLinearMap.adjoint_inner_left A.1 ψ.1 ψ.1

/-- The real observable expectation in a rank-one density operator agrees with the lossless real
vector-state expectation. -/
@[simp]
theorem DensityOperator.observableExpectation_pure
    (ψ : StateVector H) (A : Observable H) :
    (pure ψ).observableExpectation A = observableExpValue A ψ := by
  apply Complex.ofReal_injective
  rw [← (pure ψ).expectation_observable A, coe_observableExpValue,
    DensityOperator.expectation_pure_observable]

namespace PureState

/-- Observable expectation of a physical pure state, evaluated by the canonical density-state API. -/
noncomputable def observableExpectation (ρ : PureState H) (A : Observable H) : ℝ :=
  ρ.1.observableExpectation A

/-- The physical pure-state observable expectation agrees with the representative-level formula. -/
@[simp]
theorem observableExpectation_ofStateVector
    (ψ : StateVector H) (A : Observable H) :
    (ofStateVector ψ).observableExpectation A = observableExpValue A ψ := by
  simpa [PureState.observableExpectation] using
    DensityOperator.observableExpectation_pure ψ A

end PureState

end QuantumTheory
