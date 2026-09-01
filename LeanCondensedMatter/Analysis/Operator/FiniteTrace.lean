import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option linter.style.header false

/-!
# Ordinary finite-dimensional operator trace

This module owns general ordinary finite-dimensional trace infrastructure for bounded endomorphisms.
The trace is bundled as a continuous complex-linear functional, with reusable cyclicity,
matrix/operator transport, and differentiation facts.

Mathlib supplies the underlying `LinearMap.trace`, finite-dimensional cyclicity, the canonical
Euclidean matrix/operator equivalence, and derivative composition machinery. This file provides the
thin analysis-level wrappers needed by downstream physics code.

No Kubo–Bastin, Středa, disorder, model-specific, trace-per-volume, or thermodynamic-limit semantics
are introduced here. Downstream physics layers apply these primitives where an ordinary finite trace
is genuinely required.
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

/-- The finite-dimensional operator trace of a matrix transported through the canonical Euclidean
matrix/operator equivalence is its ordinary matrix trace. -/
theorem finiteDimensionalOperatorTrace_toEuclideanCLM
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    finiteDimensionalOperatorTrace
        ((Matrix.toEuclideanCLM :
          Matrix (Fin n) (Fin n) ℂ ≃⋆ₐ[ℂ]
            (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))) M) =
      Matrix.trace M := by
  rw [finiteDimensionalOperatorTrace_apply]
  let φ :
      Matrix (Fin n) (Fin n) ℂ ≃⋆ₐ[ℂ]
        (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
    Matrix.toEuclideanCLM
  have hcoe :
      ((φ M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
        EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) =
          Matrix.toEuclideanLin M := by
    simpa [φ] using Matrix.coe_toEuclideanCLM_eq_toEuclideanLin M
  change LinearMap.trace ℂ (EuclideanSpace ℂ (Fin n))
      ((φ M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
        EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) = Matrix.trace M
  rw [hcoe, Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact Matrix.trace_toLin_eq M (EuclideanSpace.basisFun (Fin n) ℂ).toBasis

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
  change HasDerivAt
    ((finiteDimensionalOperatorTrace (H := H)) ∘ operatorPath)
    (finiteDimensionalOperatorTrace (H := H) operatorDerivative)
    energy
  simpa using htrace.comp_hasDerivAt energy hoperator

end

end QuantumTheory.Transport
