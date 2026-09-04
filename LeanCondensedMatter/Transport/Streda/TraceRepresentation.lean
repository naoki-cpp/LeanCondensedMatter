import LeanCondensedMatter.Transport.Streda.Integration
import LeanCondensedMatter.Transport.Streda.TraceKernel

set_option linter.style.header false

/-!
# Traced finite-dimensional data for the regularized Středa split

The transport layer supplies a smooth operator-valued surface primitive, its exact real-energy
derivative, a canonical static Bastin integrand, and a residual sea kernel. In finite dimension the
ordinary trace turns these into scalar energy kernels. This module inserts those traced kernels into
`RegularizedStredaIntegralData`.

The remaining hypotheses are deliberately visible: the occupation and its derivative, integrability
of the occupation derivative, the integration-by-parts boundary condition, and equality of a chosen
response with the canonical traced Bastin energy integral. Integrability of the canonical traced
surface derivative and occupied surface/sea products is derived from positive-broadening kernel
continuity rather than supplied separately. The response equality is not inferred from the
finite-frequency response proved earlier in the field layer.

No zero-broadening, DC, disorder, trace-per-unit-volume, magnetic-density derivative, or
thermodynamic-limit statement is made.
-/

namespace QuantumTheory
namespace Transport

open MeasureTheory QuantumTheory.Transport

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]

/-- Analytic hypotheses needed to instantiate `RegularizedStredaIntegralData` with the canonical
finite-dimensional traced resolvent kernels. Integrability of the canonical traced kernels and their
products with the continuous occupation is derived automatically. -/
structure TracedStredaAnalyticData
    (hamiltonian current₁ current₂ : H →L[ℂ] H)
    (broadening lowerEnergy upperEnergy : ℝ)
    (occupation occupationDerivative : ℝ → ℂ) where
  /-- The Hamiltonian used in the resolvents is self-adjoint. -/
  hamiltonian_selfAdjoint : IsSelfAdjoint hamiltonian
  /-- The resolvent broadening is strictly positive. -/
  broadening_pos : 0 < broadening
  occupation_continuous :
    ContinuousOn occupation (Set.uIcc lowerEnergy upperEnergy)
  occupation_hasDerivAt :
    ∀ energy ∈ Set.Ioo (min lowerEnergy upperEnergy) (max lowerEnergy upperEnergy),
      HasDerivAt occupation (occupationDerivative energy) energy
  occupationDerivative_intervalIntegrable :
    IntervalIntegrable occupationDerivative volume lowerEnergy upperEnergy
  /-- Explicit vanishing of the finite-interval integration-by-parts boundary term. -/
  boundary_vanishes :
    occupation upperEnergy *
        regularizedStredaSurfacePrimitiveTrace
          hamiltonian current₁ current₂ upperEnergy broadening -
      occupation lowerEnergy *
        regularizedStredaSurfacePrimitiveTrace
          hamiltonian current₁ current₂ lowerEnergy broadening = 0

/-- The canonical finite-interval traced Bastin energy integral associated with the supplied
occupation. -/
noncomputable def regularizedTracedBastinEnergyIntegral
    (hamiltonian current₁ current₂ : H →L[ℂ] H)
    (broadening lowerEnergy upperEnergy : ℝ)
    (occupation : ℝ → ℂ) : ℂ :=
  ∫ energy in lowerEnergy..upperEnergy,
    occupation energy *
      regularizedBastinTraceIntegrand
        hamiltonian current₁ current₂ energy broadening

/-- Insert the canonical traced resolvent primitive and residual kernel into the abstract analytic
Středa integration data. -/
noncomputable def TracedStredaAnalyticData.toRegularizedStredaIntegralData
    {hamiltonian current₁ current₂ : H →L[ℂ] H}
    {broadening lowerEnergy upperEnergy : ℝ}
    {occupation occupationDerivative : ℝ → ℂ}
    (data : TracedStredaAnalyticData hamiltonian current₁ current₂
      broadening lowerEnergy upperEnergy occupation occupationDerivative) :
    RegularizedStredaIntegralData where
  lowerEnergy := lowerEnergy
  upperEnergy := upperEnergy
  occupation := occupation
  occupationDerivative := occupationDerivative
  surfacePrimitive := fun energy =>
    regularizedStredaSurfacePrimitiveTrace
      hamiltonian current₁ current₂ energy broadening
  surfacePrimitiveDerivative := fun energy =>
    regularizedStredaSurfacePrimitiveTraceDerivative
      hamiltonian current₁ current₂ energy broadening
  seaKernel := fun energy =>
    regularizedStredaResidualSeaTraceKernel
      hamiltonian current₁ current₂ energy broadening
  occupation_continuous := data.occupation_continuous
  surfacePrimitive_continuous := fun energy _ =>
    (hasDerivAt_regularizedStredaSurfacePrimitiveTrace
      hamiltonian data.hamiltonian_selfAdjoint current₁ current₂
      energy broadening data.broadening_pos).continuousAt.continuousWithinAt
  occupation_hasDerivAt := data.occupation_hasDerivAt
  surfacePrimitive_hasDerivAt := fun energy _ =>
    hasDerivAt_regularizedStredaSurfacePrimitiveTrace
      hamiltonian data.hamiltonian_selfAdjoint current₁ current₂
      energy broadening data.broadening_pos
  occupationDerivative_intervalIntegrable :=
    data.occupationDerivative_intervalIntegrable
  surfacePrimitiveDerivative_intervalIntegrable :=
    ContinuousOn.intervalIntegrable
      (continuous_regularizedStredaSurfacePrimitiveTraceDerivative_energy
        hamiltonian data.hamiltonian_selfAdjoint current₁ current₂
        broadening data.broadening_pos).continuousOn
  surfaceProduct_intervalIntegrable :=
    ContinuousOn.intervalIntegrable
      (data.occupation_continuous.mul
        (continuous_regularizedStredaSurfacePrimitiveTraceDerivative_energy
          hamiltonian data.hamiltonian_selfAdjoint current₁ current₂
          broadening data.broadening_pos).continuousOn)
  seaProduct_intervalIntegrable :=
    ContinuousOn.intervalIntegrable
      (data.occupation_continuous.mul
        (continuous_regularizedStredaResidualSeaTraceKernel_energy
          hamiltonian data.hamiltonian_selfAdjoint current₁ current₂
          broadening data.broadening_pos).continuousOn)
  boundary_vanishes := data.boundary_vanishes

/-- The abstract Bastin integral of the instantiated data is exactly the canonical traced Bastin
energy integral. -/
theorem TracedStredaAnalyticData.regularizedBastinEnergyIntegral_eq_traced
    {hamiltonian current₁ current₂ : H →L[ℂ] H}
    {broadening lowerEnergy upperEnergy : ℝ}
    {occupation occupationDerivative : ℝ → ℂ}
    (data : TracedStredaAnalyticData hamiltonian current₁ current₂
      broadening lowerEnergy upperEnergy occupation occupationDerivative) :
    regularizedBastinEnergyIntegral data.toRegularizedStredaIntegralData =
      regularizedTracedBastinEnergyIntegral
        hamiltonian current₁ current₂ broadening
          lowerEnergy upperEnergy occupation := by
  unfold regularizedBastinEnergyIntegral regularizedTracedBastinEnergyIntegral
    TracedStredaAnalyticData.toRegularizedStredaIntegralData
  simp_rw [regularizedBastinTraceIntegrand_eq_surfaceDerivative_add_residualSea]

/-- A chosen response becomes a concrete Středa representation once its equality with the
canonical traced Bastin energy integral is supplied explicitly. -/
noncomputable def TracedStredaAnalyticData.toRegularizedStredaRepresentation
    {hamiltonian current₁ current₂ : H →L[ℂ] H}
    {broadening lowerEnergy upperEnergy : ℝ}
    {occupation occupationDerivative : ℝ → ℂ}
    (data : TracedStredaAnalyticData hamiltonian current₁ current₂
      broadening lowerEnergy upperEnergy occupation occupationDerivative)
    (response : ℂ)
    (response_eq_tracedBastin :
      response = regularizedTracedBastinEnergyIntegral
        hamiltonian current₁ current₂ broadening
          lowerEnergy upperEnergy occupation) :
    RegularizedStredaRepresentation response where
  toRegularizedStredaIntegralData := data.toRegularizedStredaIntegralData
  response_eq_energyIntegral :=
    response_eq_tracedBastin.trans
      data.regularizedBastinEnergyIntegral_eq_traced.symm

/-- The explicit response-identification hypothesis and the stored analytic assumptions imply the
named regularized surface-plus-sea identity. -/
theorem TracedStredaAnalyticData.response_eq_surface_add_sea
    {hamiltonian current₁ current₂ : H →L[ℂ] H}
    {broadening lowerEnergy upperEnergy : ℝ}
    {occupation occupationDerivative : ℝ → ℂ}
    (data : TracedStredaAnalyticData hamiltonian current₁ current₂
      broadening lowerEnergy upperEnergy occupation occupationDerivative)
    (response : ℂ)
    (response_eq_tracedBastin :
      response = regularizedTracedBastinEnergyIntegral
        hamiltonian current₁ current₂ broadening
          lowerEnergy upperEnergy occupation) :
    response =
      regularizedStredaFermiSurface data.toRegularizedStredaIntegralData +
        regularizedStredaFermiSea data.toRegularizedStredaIntegralData :=
  (data.toRegularizedStredaRepresentation
    response response_eq_tracedBastin).response_eq_surface_add_sea

end
end Transport
end QuantumTheory
