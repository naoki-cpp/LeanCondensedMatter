import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option linter.style.header false

/-!
# Ordinary finite-dimensional operator trace

This module owns general ordinary finite-dimensional trace infrastructure for bounded endomorphisms.
The trace is bundled as a continuous complex-linear functional, with reusable cyclicity and
differentiation facts.

Mathlib supplies the underlying `LinearMap.trace`, finite-dimensional cyclicity, and derivative
composition machinery, but does not currently bundle this operator trace as a continuous linear
functional. This file provides that thin analysis-level wrapper.

No Kubo–Bastin, Středa, disorder, model-specific, trace-per-volume, or thermodynamic-limit semantics
are introduced here. Downstream physics layers apply this primitive where an ordinary finite trace is
genuinely required.
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
  have htrace :
      HasFDerivAt (finiteDimensionalOperatorTrace (H := H))
        ((finiteDimensionalOperatorTrace (H := H)).restrictScalars ℝ)
        (operatorPath energy) :=
    ((finiteDimensionalOperatorTrace (H := H)).hasFDerivAt).restrictScalars ℝ
  simpa using htrace.comp_hasDerivAt energy hoperator

end

end QuantumTheory.Transport
