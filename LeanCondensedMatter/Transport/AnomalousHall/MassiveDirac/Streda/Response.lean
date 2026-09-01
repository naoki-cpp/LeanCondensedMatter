import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Operator
import LeanCondensedMatter.Transport.Streda.TraceKernel

set_option linter.style.header false

/-!
# Massive-Dirac Bastin/Středa trace specialization

The massive-Dirac matrix model and its bounded-operator realization are owned by
`MassiveDirac/Model`. This module now contains only the model-specific specialization of the generic
pointwise Bastin/Středa trace identity to the clean Hamiltonian and physical `x-y` charge-current
vertices.

No eigenvector gauge, spectral-projector expansion, finite-broadening limit, or continuum momentum
normalization is introduced here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Pointwise finite-broadening Bastin/Středa identity specialized to the massive-Dirac Hamiltonian
and the `x-y` Hall-current vertices. -/
theorem regularizedBastinTraceIntegrand_eq_streda
    (e v m px py energy broadening : ℝ) :
    regularizedBastinTraceIntegrand
        (hamiltonianOperator v m px py)
        (currentOperator .x e v) (currentOperator .y e v) energy broadening =
      regularizedStredaSurfacePrimitiveTraceDerivative
          (hamiltonianOperator v m px py)
          (currentOperator .x e v) (currentOperator .y e v) energy broadening +
        regularizedStredaResidualSeaTraceKernel
          (hamiltonianOperator v m px py)
          (currentOperator .x e v) (currentOperator .y e v) energy broadening :=
  QuantumTheory.Transport.regularizedBastinTraceIntegrand_eq_surfaceDerivative_add_residualSea
    (hamiltonianOperator v m px py)
    (currentOperator .x e v) (currentOperator .y e v) energy broadening

end

end AnomalousHall.MassiveDirac
