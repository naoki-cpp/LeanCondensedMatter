import LeanCondensedMatter.Transport.StredaOperatorKernel
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option linter.style.header false

/-!
# Finite-dimensional trace kernels for the regularized Středa split

The operator-valued kernels in `StredaOperatorKernel` become the scalar energy kernels used by a
finite Kubo–Bastin formula only after applying an ordinary finite-dimensional trace. This module
bundles that trace as a continuous complex-linear functional on bounded endomorphisms and proves
that:

* differentiation of a real-energy operator path commutes with the trace;
* the traced surface primitive has the traced operator derivative;
* the operator pointwise Bastin decomposition descends to scalar trace kernels; and
* ordinary finite-dimensional cyclicity remains available explicitly.

No occupation integral or identification with the finite-frequency response from the field layer
is made here. Zero broadening, DC, disorder, trace per unit volume, magnetic derivatives, and the
thermodynamic limit remain outside this module.
-/

namespace QuantumTheory.Transport

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

/-- Ordinary finite-dimensional trace, bundled as a continuous linear functional on bounded
endomorphisms. Continuity follows because the bounded-endomorphism space is finite-dimensional. -/
noncomputable def finiteDimensionalOperatorTrace :
    (H →L[ℂ] H) →L[ℂ] ℂ :=
  ((LinearMap.trace ℂ H).comp (ContinuousLinearMap.coeLM ℂ)).toContinuousLinearMap

@[simp]
theorem finiteDimensionalOperatorTrace_apply (operator : H →L[ℂ] H) :
    finiteDimensionalOperatorTrace (H := H) operator =
      LinearMap.trace ℂ H (operator : H →ₗ[ℂ] H) :=
  rfl

/-- Cyclicity of the bundled ordinary trace for two bounded endomorphisms. -/
theorem finiteDimensionalOperatorTrace_mul_comm
    (left right : H →L[ℂ] H) :
    finiteDimensionalOperatorTrace (H := H) (left * right) =
      finiteDimensionalOperatorTrace (H := H) (right * left) := by
  simp only [finiteDimensionalOperatorTrace_apply]
  exact LinearMap.trace_mul_comm ℂ (left : H →ₗ[ℂ] H) (right : H →ₗ[ℂ] H)

/-- Applying the finite-dimensional trace to a differentiable real-energy operator path preserves
its derivative. -/
theorem hasDerivAt_finiteDimensionalOperatorTrace_comp
    {operatorPath : ℝ → H →L[ℂ] H} {operatorDerivative : H →L[ℂ] H}
    {energy : ℝ} (hoperator : HasDerivAt operatorPath operatorDerivative energy) :
    HasDerivAt
      (fun x : ℝ => finiteDimensionalOperatorTrace (H := H) (operatorPath x))
      (finiteDimensionalOperatorTrace (H := H) operatorDerivative)
      energy := by
  have houter : HasFDerivAt (finiteDimensionalOperatorTrace (H := H))
      ((finiteDimensionalOperatorTrace (H := H)).restrictScalars ℝ)
      (operatorPath energy) :=
    ((finiteDimensionalOperatorTrace (H := H)).hasFDerivAt).restrictScalars ℝ
  have hcomp := (houter.comp energy hoperator.hasFDerivAt).hasDerivAt
  have hvalue :
      ((((finiteDimensionalOperatorTrace (H := H)).restrictScalars ℝ) ∘SL
        ContinuousLinearMap.toSpanSingleton ℝ operatorDerivative) 1) =
        finiteDimensionalOperatorTrace (H := H) operatorDerivative := by
    simp
  rw [hvalue] at hcomp
  change HasDerivAt
    ((finiteDimensionalOperatorTrace (H := H)) ∘ operatorPath)
    (finiteDimensionalOperatorTrace (H := H) operatorDerivative)
    energy
  exact hcomp

/-- Scalar trace of the regularized Středa surface primitive. -/
noncomputable def regularizedStredaSurfacePrimitiveTrace
    (hamiltonian current₁ current₂ : H →L[ℂ] H)
    (energy broadening : ℝ) : ℂ :=
  finiteDimensionalOperatorTrace (H := H)
    (regularizedStredaSurfacePrimitiveOperator
      hamiltonian current₁ current₂ energy broadening)

/-- Scalar trace of the exact derivative of the regularized Středa surface primitive. -/
noncomputable def regularizedStredaSurfacePrimitiveTraceDerivative
    (hamiltonian current₁ current₂ : H →L[ℂ] H)
    (energy broadening : ℝ) : ℂ :=
  finiteDimensionalOperatorTrace (H := H)
    (regularizedStredaSurfacePrimitiveOperatorDerivative
      hamiltonian current₁ current₂ energy broadening)

/-- Scalar ordinary-trace form of the canonical static regularized Bastin integrand. -/
noncomputable def regularizedBastinTraceIntegrand
    (hamiltonian current₁ current₂ : H →L[ℂ] H)
    (energy broadening : ℝ) : ℂ :=
  finiteDimensionalOperatorTrace (H := H)
    (regularizedBastinOperatorIntegrand
      hamiltonian current₁ current₂ energy broadening)

/-- Scalar ordinary-trace form of the finite-broadening residual sea kernel. -/
noncomputable def regularizedStredaResidualSeaTraceKernel
    (hamiltonian current₁ current₂ : H →L[ℂ] H)
    (energy broadening : ℝ) : ℂ :=
  finiteDimensionalOperatorTrace (H := H)
    (regularizedStredaResidualSeaOperatorKernel
      hamiltonian current₁ current₂ energy broadening)

/-- The traced surface primitive has the traced operator derivative at every positive broadening. -/
theorem hasDerivAt_regularizedStredaSurfacePrimitiveTrace
    [CompleteSpace H]
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (current₁ current₂ : H →L[ℂ] H)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    HasDerivAt
      (fun x : ℝ => regularizedStredaSurfacePrimitiveTrace
        hamiltonian current₁ current₂ x broadening)
      (regularizedStredaSurfacePrimitiveTraceDerivative
        hamiltonian current₁ current₂ energy broadening)
      energy := by
  unfold regularizedStredaSurfacePrimitiveTrace
    regularizedStredaSurfacePrimitiveTraceDerivative
  exact hasDerivAt_finiteDimensionalOperatorTrace_comp
    (hasDerivAt_regularizedStredaSurfacePrimitiveOperator
      hamiltonian hself current₁ current₂ energy broadening hbroadening)

/-- The pointwise operator decomposition descends to the ordinary finite-dimensional trace. -/
theorem regularizedBastinTraceIntegrand_eq_surfaceDerivative_add_residualSea
    (hamiltonian current₁ current₂ : H →L[ℂ] H)
    (energy broadening : ℝ) :
    regularizedBastinTraceIntegrand
        hamiltonian current₁ current₂ energy broadening =
      regularizedStredaSurfacePrimitiveTraceDerivative
          hamiltonian current₁ current₂ energy broadening +
        regularizedStredaResidualSeaTraceKernel
          hamiltonian current₁ current₂ energy broadening := by
  unfold regularizedBastinTraceIntegrand
    regularizedStredaSurfacePrimitiveTraceDerivative
    regularizedStredaResidualSeaTraceKernel
  rw [regularizedBastinOperatorIntegrand_eq_surfaceDerivative_add_residualSea]
  exact map_add (finiteDimensionalOperatorTrace (H := H)) _ _

end

end QuantumTheory.Transport
