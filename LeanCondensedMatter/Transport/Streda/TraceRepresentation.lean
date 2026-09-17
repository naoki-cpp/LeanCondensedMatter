import LeanCondensedMatter.Transport.Streda.Integration
import LeanCondensedMatter.Transport.Streda.TraceKernel

set_option linter.style.header false

/-!
# Traced finite-dimensional data for the regularized Středa split

The transport layer supplies a smooth operator-valued surface primitive, its exact real-energy
derivative, a canonical static Bastin integrand, and a residual sea kernel. In finite dimension the
ordinary trace turns these into scalar energy kernels. This module inserts those traced kernels into
`RegularizedStredaIntegralData`.

`TracedStredaKernelFacts` owns the Hamiltonian, broadening, and occupation regularity shared by every
current pair in one traced Středa calculation. The pair-specific adapter adds only the
integration-by-parts boundary condition. Integrability of the canonical traced surface derivative
and occupied surface/sea products is derived once from the shared facts and the trace-kernel
continuity theorems.

A chosen response still becomes a representation only after an explicit equality with the canonical
traced Bastin energy integral is supplied. No zero-broadening, DC, disorder, trace-per-unit-volume,
magnetic-density derivative, or thermodynamic-limit statement is made.
-/

namespace QuantumTheory
namespace Transport

open MeasureTheory QuantumTheory.Transport

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]

/-- Shared analytic provenance for canonical finite-dimensional traced Středa kernels.

These facts are independent of the ordered current pair. Pair-dependent boundary conditions are
attached only when constructing concrete integral data. -/
structure TracedStredaKernelFacts
    (hamiltonian : H →L[ℂ] H)
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

/-- Analytic hypotheses for one ordered current pair. Shared traced-kernel provenance is inherited
from `TracedStredaKernelFacts`; only the boundary condition depends on the pair. -/
structure TracedStredaAnalyticData
    (hamiltonian current₁ current₂ : H →L[ℂ] H)
    (broadening lowerEnergy upperEnergy : ℝ)
    (occupation occupationDerivative : ℝ → ℂ)
    extends TracedStredaKernelFacts hamiltonian broadening lowerEnergy upperEnergy
      occupation occupationDerivative where
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

/-- Instantiate the abstract Středa integration data for an ordered current pair from one shared set
of traced-kernel facts and that pair's boundary condition. -/
noncomputable def TracedStredaKernelFacts.toRegularizedStredaIntegralData
    {hamiltonian : H →L[ℂ] H}
    {broadening lowerEnergy upperEnergy : ℝ}
    {occupation occupationDerivative : ℝ → ℂ}
    (facts : TracedStredaKernelFacts hamiltonian broadening lowerEnergy upperEnergy
      occupation occupationDerivative)
    (current₁ current₂ : H →L[ℂ] H)
    (boundary_vanishes :
      occupation upperEnergy *
          regularizedStredaSurfacePrimitiveTrace
            hamiltonian current₁ current₂ upperEnergy broadening -
        occupation lowerEnergy *
          regularizedStredaSurfacePrimitiveTrace
            hamiltonian current₁ current₂ lowerEnergy broadening = 0) :
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
  occupation_continuous := facts.occupation_continuous
  surfacePrimitive_continuous := fun energy _ =>
    (hasDerivAt_regularizedStredaSurfacePrimitiveTrace
      hamiltonian facts.hamiltonian_selfAdjoint current₁ current₂
      energy broadening facts.broadening_pos).continuousAt.continuousWithinAt
  occupation_hasDerivAt := facts.occupation_hasDerivAt
  surfacePrimitive_hasDerivAt := fun energy _ =>
    hasDerivAt_regularizedStredaSurfacePrimitiveTrace
      hamiltonian facts.hamiltonian_selfAdjoint current₁ current₂
      energy broadening facts.broadening_pos
  occupationDerivative_intervalIntegrable :=
    facts.occupationDerivative_intervalIntegrable
  surfacePrimitiveDerivative_intervalIntegrable :=
    ContinuousOn.intervalIntegrable
      (continuous_regularizedStredaSurfacePrimitiveTraceDerivative_energy
        hamiltonian facts.hamiltonian_selfAdjoint current₁ current₂
        broadening facts.broadening_pos).continuousOn
  surfaceProduct_intervalIntegrable :=
    ContinuousOn.intervalIntegrable
      (facts.occupation_continuous.mul
        (continuous_regularizedStredaSurfacePrimitiveTraceDerivative_energy
          hamiltonian facts.hamiltonian_selfAdjoint current₁ current₂
          broadening facts.broadening_pos).continuousOn)
  seaProduct_intervalIntegrable :=
    ContinuousOn.intervalIntegrable
      (facts.occupation_continuous.mul
        (continuous_regularizedStredaResidualSeaTraceKernel_energy
          hamiltonian facts.hamiltonian_selfAdjoint current₁ current₂
          broadening facts.broadening_pos).continuousOn)
  boundary_vanishes := boundary_vanishes

/-- Insert the canonical traced resolvent primitive and residual kernel into the abstract analytic
Středa integration data. -/
noncomputable def TracedStredaAnalyticData.toRegularizedStredaIntegralData
    {hamiltonian current₁ current₂ : H →L[ℂ] H}
    {broadening lowerEnergy upperEnergy : ℝ}
    {occupation occupationDerivative : ℝ → ℂ}
    (data : TracedStredaAnalyticData hamiltonian current₁ current₂
      broadening lowerEnergy upperEnergy occupation occupationDerivative) :
    RegularizedStredaIntegralData :=
  data.toTracedStredaKernelFacts.toRegularizedStredaIntegralData
    current₁ current₂ data.boundary_vanishes

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
    TracedStredaKernelFacts.toRegularizedStredaIntegralData
  simp_rw [regularizedBastinTraceIntegrand_eq_surfaceDerivative_add_residualSea]

/-- A traced Bastin energy integral with identically zero occupation derivative is carried entirely
by the residual Fermi-sea term. -/
theorem TracedStredaAnalyticData.regularizedTracedBastinEnergyIntegral_eq_sea_of_derivative_zero
    {hamiltonian current₁ current₂ : H →L[ℂ] H}
    {broadening lowerEnergy upperEnergy : ℝ}
    {occupation occupationDerivative : ℝ → ℂ}
    (data : TracedStredaAnalyticData hamiltonian current₁ current₂
      broadening lowerEnergy upperEnergy occupation occupationDerivative)
    (hzero : occupationDerivative = fun _ => 0) :
    regularizedTracedBastinEnergyIntegral
        hamiltonian current₁ current₂ broadening lowerEnergy upperEnergy occupation =
      regularizedStredaFermiSea data.toRegularizedStredaIntegralData := by
  rw [← data.regularizedBastinEnergyIntegral_eq_traced]
  exact regularizedBastinEnergyIntegral_eq_sea_of_occupationDerivative_eq_zero
    data.toRegularizedStredaIntegralData hzero

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

end
end Transport
end QuantumTheory
