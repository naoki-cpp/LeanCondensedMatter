import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Operator
import LeanCondensedMatter.Transport.Streda.TraceRepresentation

set_option linter.style.header false

/-!
# Finite-broadening massive-Dirac longitudinal response with a dressed current vertex

This module is the longitudinal response bridge between an explicitly supplied in-plane current
vertex and the generic finite-broadening Kubo–Bastin/Středa stack.  The measured vertex is the
physical bare longitudinal charge current `jₓ`; the source vertex is the model-owned in-plane linear
combination `α jₓ + β jᵧ`.

Keeping the two coefficients independent preserves the finite-broadening `σₓ` / `σᵧ` structure of
the Born retarded-advanced rung.  No ladder solution or weak-disorder scalar replacement is made
here.  In particular, the factor `(1 - λₓ)⁻¹` derived in the weak-disorder layer is not inserted by
definition.

The resulting traced Bastin energy integral is split by the existing generic
`TracedStredaAnalyticData` boundary.  All occupation regularity, finite-energy endpoint, and positive
broadening hypotheses therefore remain visible.  No zero-broadening, clean-DC, exact disorder
average, SCBA/Ward, crossed-diagram, or thermodynamic-limit claim is introduced.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Pointwise finite-broadening traced Bastin kernel for a bare measured `jₓ` and a supplied dressed
in-plane source current.  This is an exact specialization of the generic trace kernel. -/
noncomputable def massiveDiracLongitudinalDressedBastinTraceIntegrand
    (e v m px py energy broadening : ℝ) (alpha beta : ℂ) : ℂ :=
  regularizedBastinTraceIntegrand
    (hamiltonianOperator v m px py)
    (currentOperator .x e v)
    (inPlaneCurrentOperator e v alpha beta)
    energy broadening

/-- Canonical traced Středa analytic data for the longitudinal channel with a supplied in-plane
dressed source vertex. -/
abbrev MassiveDiracLongitudinalDressedStredaAnalyticData
    (e v m px py broadening lowerEnergy upperEnergy : ℝ)
    (alpha beta : ℂ)
    (occupation occupationDerivative : ℝ → ℂ) :=
  TracedStredaAnalyticData
    (hamiltonianOperator v m px py)
    (currentOperator .x e v)
    (inPlaneCurrentOperator e v alpha beta)
    broadening lowerEnergy upperEnergy occupation occupationDerivative

/-- Finite-energy regularized traced Bastin response of one massive-Dirac momentum fiber with a
supplied in-plane dressed source current. -/
noncomputable def massiveDiracLongitudinalDressedBastinEnergyIntegral
    (e v m px py broadening lowerEnergy upperEnergy : ℝ)
    (alpha beta : ℂ) (occupation : ℝ → ℂ) : ℂ :=
  regularizedTracedBastinEnergyIntegral
    (hamiltonianOperator v m px py)
    (currentOperator .x e v)
    (inPlaneCurrentOperator e v alpha beta)
    broadening lowerEnergy upperEnergy occupation

/-- Named finite-broadening Fermi-surface contribution for the longitudinal dressed-current
channel. -/
noncomputable def massiveDiracLongitudinalDressedStredaFermiSurface
    {e v m px py broadening lowerEnergy upperEnergy : ℝ}
    {alpha beta : ℂ} {occupation occupationDerivative : ℝ → ℂ}
    (data : MassiveDiracLongitudinalDressedStredaAnalyticData
      e v m px py broadening lowerEnergy upperEnergy alpha beta
      occupation occupationDerivative) : ℂ :=
  regularizedStredaFermiSurface data.toRegularizedStredaIntegralData

/-- Named finite-broadening residual Fermi-sea contribution for the same dressed-current channel. -/
noncomputable def massiveDiracLongitudinalDressedStredaFermiSea
    {e v m px py broadening lowerEnergy upperEnergy : ℝ}
    {alpha beta : ℂ} {occupation occupationDerivative : ℝ → ℂ}
    (data : MassiveDiracLongitudinalDressedStredaAnalyticData
      e v m px py broadening lowerEnergy upperEnergy alpha beta
      occupation occupationDerivative) : ℂ :=
  regularizedStredaFermiSea data.toRegularizedStredaIntegralData

/-- The longitudinal dressed-current surface channel is exactly the occupation-derivative term with
bare measured `jₓ` and the supplied dressed source vertex kept inside the finite-broadening surface
primitive. -/
theorem massiveDiracLongitudinalDressedStredaFermiSurface_eq
    {e v m px py broadening lowerEnergy upperEnergy : ℝ}
    {alpha beta : ℂ} {occupation occupationDerivative : ℝ → ℂ}
    (data : MassiveDiracLongitudinalDressedStredaAnalyticData
      e v m px py broadening lowerEnergy upperEnergy alpha beta
      occupation occupationDerivative) :
    massiveDiracLongitudinalDressedStredaFermiSurface data =
      -(∫ energy in lowerEnergy..upperEnergy,
        occupationDerivative energy *
          regularizedStredaSurfacePrimitiveTrace
            (hamiltonianOperator v m px py)
            (currentOperator .x e v)
            (inPlaneCurrentOperator e v alpha beta)
            energy broadening) := by
  rfl

/-- The residual sea channel retains the same supplied dressed current vertex and finite
broadening. -/
theorem massiveDiracLongitudinalDressedStredaFermiSea_eq
    {e v m px py broadening lowerEnergy upperEnergy : ℝ}
    {alpha beta : ℂ} {occupation occupationDerivative : ℝ → ℂ}
    (data : MassiveDiracLongitudinalDressedStredaAnalyticData
      e v m px py broadening lowerEnergy upperEnergy alpha beta
      occupation occupationDerivative) :
    massiveDiracLongitudinalDressedStredaFermiSea data =
      ∫ energy in lowerEnergy..upperEnergy,
        occupation energy *
          regularizedStredaResidualSeaTraceKernel
            (hamiltonianOperator v m px py)
            (currentOperator .x e v)
            (inPlaneCurrentOperator e v alpha beta)
            energy broadening := by
  rfl

/-- Under the generic visible analytic hypotheses, the actual dressed-current longitudinal traced
Bastin energy integral is exactly its named finite-broadening Fermi-surface plus residual sea
contributions. -/
theorem massiveDiracLongitudinalDressedBastinEnergyIntegral_eq_surface_add_sea
    {e v m px py broadening lowerEnergy upperEnergy : ℝ}
    {alpha beta : ℂ} {occupation occupationDerivative : ℝ → ℂ}
    (data : MassiveDiracLongitudinalDressedStredaAnalyticData
      e v m px py broadening lowerEnergy upperEnergy alpha beta
      occupation occupationDerivative) :
    massiveDiracLongitudinalDressedBastinEnergyIntegral
        e v m px py broadening lowerEnergy upperEnergy alpha beta occupation =
      massiveDiracLongitudinalDressedStredaFermiSurface data +
        massiveDiracLongitudinalDressedStredaFermiSea data := by
  unfold massiveDiracLongitudinalDressedBastinEnergyIntegral
  rw [← data.regularizedBastinEnergyIntegral_eq_traced]
  exact regularizedBastinEnergyIntegral_eq_surface_add_sea
    data.toRegularizedStredaIntegralData

end

end AnomalousHall.MassiveDirac
