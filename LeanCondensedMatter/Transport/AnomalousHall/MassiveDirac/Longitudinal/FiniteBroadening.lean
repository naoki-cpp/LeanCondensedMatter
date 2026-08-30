import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Model.Operator
import LeanCondensedMatter.Transport.Streda.TraceRepresentation

set_option linter.style.header false

/-!
# Finite-broadening massive-Dirac longitudinal response with a dressed current vertex

This module is the operator/channel bridge between the massive-Dirac current-vertex work and the
generic finite-broadening Kubo–Bastin/Středa stack.  The measured vertex is the physical bare
longitudinal charge current `jₓ`; the source vertex is kept as an arbitrary in-plane linear
combination of the physical `x` and `y` charge currents.

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

/-- Dimensionless in-plane Pauli vertex `α σₓ + β σᵧ` as a bounded operator. -/
noncomputable def inPlanePauliVertexOperator
    (alpha beta : ℂ) : DiracHilbert →L[ℂ] DiracHilbert :=
  alpha • matrixOperator sigmaX + beta • matrixOperator sigmaY

@[simp] theorem inPlanePauliVertexOperator_one_zero :
    inPlanePauliVertexOperator 1 0 = matrixOperator sigmaX := by
  simp [inPlanePauliVertexOperator]

@[simp] theorem inPlanePauliVertexOperator_zero_one :
    inPlanePauliVertexOperator 0 1 = matrixOperator sigmaY := by
  simp [inPlanePauliVertexOperator]

/-- Physical in-plane dressed charge-current vertex.  The coefficients multiply the canonical
massive-Dirac physical current operators, so `alpha = 1`, `beta = 0` is exactly the bare
longitudinal `x` current. -/
noncomputable def dressedLongitudinalCurrentOperator
    (e v : ℝ) (alpha beta : ℂ) : DiracHilbert →L[ℂ] DiracHilbert :=
  alpha • currentOperator .x e v + beta • currentOperator .y e v

/-- The physical dressed current is electron charge times the Dirac velocity scale multiplying the
dimensionless in-plane Pauli vertex.  This is the exact operator bridge from the `σₓ` / `σᵧ`
vertex coefficients used by the Born rung to the physical current convention. -/
theorem dressedLongitudinalCurrentOperator_eq_chargeVelocity_smul_inPlanePauliVertexOperator
    (e v : ℝ) (alpha beta : ℂ) :
    dressedLongitudinalCurrentOperator e v alpha beta =
      (((-e * v : ℝ) : ℂ)) • inPlanePauliVertexOperator alpha beta := by
  have hx :
      currentOperator .x e v =
        (((-e * v : ℝ) : ℂ)) • matrixOperator sigmaX := by
    simp [currentOperator, current, velocity, directionPauli, matrixOperator, map_smul,
      smul_smul]
  have hy :
      currentOperator .y e v =
        (((-e * v : ℝ) : ℂ)) • matrixOperator sigmaY := by
    simp [currentOperator, current, velocity, directionPauli, matrixOperator, map_smul,
      smul_smul]
  rw [dressedLongitudinalCurrentOperator, hx, hy]
  simp [inPlanePauliVertexOperator, smul_add, smul_smul, mul_comm]

/-- The undressed in-plane coefficient pair recovers the repository's canonical longitudinal
charge-current operator exactly. -/
@[simp] theorem dressedLongitudinalCurrentOperator_one_zero
    (e v : ℝ) :
    dressedLongitudinalCurrentOperator e v 1 0 = currentOperator .x e v := by
  simp [dressedLongitudinalCurrentOperator]

@[simp] theorem dressedLongitudinalCurrentOperator_zero_one
    (e v : ℝ) :
    dressedLongitudinalCurrentOperator e v 0 1 = currentOperator .y e v := by
  simp [dressedLongitudinalCurrentOperator]

/-- Pointwise finite-broadening traced Bastin kernel for a bare measured `jₓ` and a supplied dressed
in-plane source current.  This is an exact specialization of the generic trace kernel. -/
noncomputable def massiveDiracLongitudinalDressedBastinTraceIntegrand
    (e v m px py energy broadening : ℝ) (alpha beta : ℂ) : ℂ :=
  regularizedBastinTraceIntegrand
    (hamiltonianOperator v m px py)
    (currentOperator .x e v)
    (dressedLongitudinalCurrentOperator e v alpha beta)
    energy broadening

/-- The bare source-vertex specialization is the ordinary longitudinal `jₓ-jₓ` Bastin trace
kernel. -/
@[simp] theorem massiveDiracLongitudinalDressedBastinTraceIntegrand_one_zero
    (e v m px py energy broadening : ℝ) :
    massiveDiracLongitudinalDressedBastinTraceIntegrand
        e v m px py energy broadening 1 0 =
      regularizedBastinTraceIntegrand
        (hamiltonianOperator v m px py)
        (currentOperator .x e v) (currentOperator .x e v)
        energy broadening := by
  simp [massiveDiracLongitudinalDressedBastinTraceIntegrand]

/-- Canonical traced Středa analytic data for the longitudinal channel with a supplied in-plane
dressed source vertex. -/
abbrev MassiveDiracLongitudinalDressedStredaAnalyticData
    (e v m px py broadening lowerEnergy upperEnergy : ℝ)
    (alpha beta : ℂ)
    (occupation occupationDerivative : ℝ → ℂ) :=
  TracedStredaAnalyticData
    (hamiltonianOperator v m px py)
    (currentOperator .x e v)
    (dressedLongitudinalCurrentOperator e v alpha beta)
    broadening lowerEnergy upperEnergy occupation occupationDerivative

/-- Finite-energy regularized traced Bastin response of one massive-Dirac momentum fiber with a
supplied in-plane dressed source current. -/
noncomputable def massiveDiracLongitudinalDressedBastinEnergyIntegral
    (e v m px py broadening lowerEnergy upperEnergy : ℝ)
    (alpha beta : ℂ) (occupation : ℝ → ℂ) : ℂ :=
  regularizedTracedBastinEnergyIntegral
    (hamiltonianOperator v m px py)
    (currentOperator .x e v)
    (dressedLongitudinalCurrentOperator e v alpha beta)
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
            (dressedLongitudinalCurrentOperator e v alpha beta)
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
            (dressedLongitudinalCurrentOperator e v alpha beta)
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

/-- Bare-vertex regression: the new dressed-current energy response reduces exactly to the generic
ordinary longitudinal `jₓ-jₓ` traced Bastin energy integral. -/
@[simp] theorem massiveDiracLongitudinalDressedBastinEnergyIntegral_one_zero
    (e v m px py broadening lowerEnergy upperEnergy : ℝ)
    (occupation : ℝ → ℂ) :
    massiveDiracLongitudinalDressedBastinEnergyIntegral
        e v m px py broadening lowerEnergy upperEnergy 1 0 occupation =
      regularizedTracedBastinEnergyIntegral
        (hamiltonianOperator v m px py)
        (currentOperator .x e v) (currentOperator .x e v)
        broadening lowerEnergy upperEnergy occupation := by
  simp [massiveDiracLongitudinalDressedBastinEnergyIntegral]

end

end AnomalousHall.MassiveDirac
