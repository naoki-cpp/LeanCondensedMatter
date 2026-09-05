import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Operator
import LeanCondensedMatter.Transport.Streda.TraceRepresentation

set_option linter.style.header false

/-!
# Finite-broadening massive-Dirac longitudinal response with a dressed current vertex

This module is the longitudinal response bridge between an explicitly supplied in-plane current
vertex and the generic finite-broadening Kubo–Bastin/Středa stack. The measured vertex is the
physical bare longitudinal charge current `jₓ`; the source vertex is the model-owned in-plane linear
combination `α jₓ + β jᵧ`.

The bridge deliberately keeps only the model-specific specialization theorem. Generic traced
Bastin kernels, analytic-data structures, and named Fermi-surface/Fermi-sea terms remain owned by
`Transport.Streda`; this module does not wrap them under duplicate MassiveDirac-specific names.

No ladder solution, zero-broadening limit, exact disorder average, SCBA/Ward claim, crossed-diagram
correction, or thermodynamic limit is introduced here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Under the generic visible analytic hypotheses, the finite-broadening longitudinal Bastin energy
integral with bare measured `jₓ` and supplied in-plane dressed source current splits exactly into
the generic Středa Fermi-surface and residual Fermi-sea contributions. -/
theorem massiveDiracLongitudinalDressedBastinEnergyIntegral_eq_surface_add_sea
    {e v m px py broadening lowerEnergy upperEnergy : ℝ}
    {alpha beta : ℂ} {occupation occupationDerivative : ℝ → ℂ}
    (data : TracedStredaAnalyticData
      (hamiltonianOperator v m px py)
      (currentOperator .x e v)
      (inPlaneCurrentOperator e v alpha beta)
      broadening lowerEnergy upperEnergy occupation occupationDerivative) :
    regularizedTracedBastinEnergyIntegral
        (hamiltonianOperator v m px py)
        (currentOperator .x e v)
        (inPlaneCurrentOperator e v alpha beta)
        broadening lowerEnergy upperEnergy occupation =
      regularizedStredaFermiSurface data.toRegularizedStredaIntegralData +
        regularizedStredaFermiSea data.toRegularizedStredaIntegralData := by
  rw [← data.regularizedBastinEnergyIntegral_eq_traced]
  exact regularizedBastinEnergyIntegral_eq_surface_add_sea
    data.toRegularizedStredaIntegralData

end

end AnomalousHall.MassiveDirac
