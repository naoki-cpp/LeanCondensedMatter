import LeanCondensedMatter.Transport.Core.FiniteTrace
import LeanCondensedMatter.Transport.Streda.OperatorKernel

set_option linter.style.header false

/-!
# Finite-dimensional trace kernels for the regularized Středa split

The operator-valued kernels in `Streda.OperatorKernel` become the scalar energy kernels used by a
finite Kubo–Bastin formula only after applying the ordinary finite-dimensional trace owned by
`Core.FiniteTrace`. This module applies that generic trace primitive to the Středa operator kernels and
proves that:

* differentiation of the real-energy Středa operator path descends through the trace;
* the traced surface primitive has the traced operator derivative; and
* the operator pointwise Bastin decomposition descends to scalar trace kernels.

No occupation integral or identification with the finite-frequency response from the field layer
is made here. Zero broadening, DC, disorder, trace per unit volume, magnetic derivatives, and the
thermodynamic limit remain outside this module.
-/

namespace QuantumTheory.Transport

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

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
