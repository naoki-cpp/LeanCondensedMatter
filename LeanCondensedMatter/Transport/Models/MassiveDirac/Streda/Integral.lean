import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.Response
import LeanCondensedMatter.Transport.Streda.TraceRepresentation

set_option linter.style.header false

/-!
# Massive-Dirac regularized Středa energy split

The massive-Dirac Bastin development already specializes the repository's pointwise regularized
Bastin/Středa identity to the physical Hamiltonian and charge-current vertices. This file lifts
that pointwise identity to the finite-energy integration-by-parts layer owned by
`Transport.StredaTraceRepresentation`.

For a differentiable occupation interpolation and fixed positive broadening, the model-specific
traced Bastin energy integral is therefore split canonically as

```text
Bastin = Fermi surface + Fermi sea,

surface = -∫ f'(E) P(E) dE,
sea     =  ∫ f(E) S(E) dE,
```

where `P` is the repository's regularized Středa surface primitive and `S` its residual sea kernel,
both evaluated on the actual massive-Dirac Hamiltonian and the `x-y` Hall-current vertices.

This remains a finite-broadening, finite-energy-interval theorem. In particular, no zero-temperature
distributional derivative, zero-broadening limit, or interchange with momentum integration is
claimed here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Canonical analytic Středa data specialized to the massive-Dirac Hamiltonian and physical
`x-y` charge-current vertices. All occupation, integrability, endpoint, and positive-broadening
hypotheses remain exactly those of the generic traced Středa layer. -/
abbrev MassiveDiracStredaAnalyticData
    (e v m px py broadening lowerEnergy upperEnergy : ℝ)
    (occupation occupationDerivative : ℝ → ℂ) :=
  TracedStredaAnalyticData
    (hamiltonianOperator v m px py)
    (currentOperator .x e v) (currentOperator .y e v)
    broadening lowerEnergy upperEnergy occupation occupationDerivative

/-- Finite-interval regularized traced Bastin energy response for one massive-Dirac momentum fiber. -/
noncomputable def massiveDiracRegularizedBastinEnergyIntegral
    (e v m px py broadening lowerEnergy upperEnergy : ℝ)
    (occupation : ℝ → ℂ) : ℂ :=
  regularizedTracedBastinEnergyIntegral
    (hamiltonianOperator v m px py)
    (currentOperator .x e v) (currentOperator .y e v)
    broadening lowerEnergy upperEnergy occupation

/-- Named Fermi-surface part of the massive-Dirac regularized Středa split. -/
noncomputable def massiveDiracRegularizedStredaFermiSurface
    {e v m px py broadening lowerEnergy upperEnergy : ℝ}
    {occupation occupationDerivative : ℝ → ℂ}
    (data : MassiveDiracStredaAnalyticData
      e v m px py broadening lowerEnergy upperEnergy occupation occupationDerivative) : ℂ :=
  regularizedStredaFermiSurface data.toRegularizedStredaIntegralData

/-- Named Fermi-sea part of the massive-Dirac regularized Středa split. -/
noncomputable def massiveDiracRegularizedStredaFermiSea
    {e v m px py broadening lowerEnergy upperEnergy : ℝ}
    {occupation occupationDerivative : ℝ → ℂ}
    (data : MassiveDiracStredaAnalyticData
      e v m px py broadening lowerEnergy upperEnergy occupation occupationDerivative) : ℂ :=
  regularizedStredaFermiSea data.toRegularizedStredaIntegralData

/-- The model-specific surface contribution is exactly the occupation-derivative term of the
repository's Středa convention. -/
theorem massiveDiracRegularizedStredaFermiSurface_eq
    {e v m px py broadening lowerEnergy upperEnergy : ℝ}
    {occupation occupationDerivative : ℝ → ℂ}
    (data : MassiveDiracStredaAnalyticData
      e v m px py broadening lowerEnergy upperEnergy occupation occupationDerivative) :
    massiveDiracRegularizedStredaFermiSurface data =
      -(∫ energy in lowerEnergy..upperEnergy,
        occupationDerivative energy *
          regularizedStredaSurfacePrimitiveTrace
            (hamiltonianOperator v m px py)
            (currentOperator .x e v) (currentOperator .y e v)
            energy broadening) := by
  rfl

/-- The model-specific sea contribution is exactly the occupied residual-sea kernel of the
repository's Středa convention. -/
theorem massiveDiracRegularizedStredaFermiSea_eq
    {e v m px py broadening lowerEnergy upperEnergy : ℝ}
    {occupation occupationDerivative : ℝ → ℂ}
    (data : MassiveDiracStredaAnalyticData
      e v m px py broadening lowerEnergy upperEnergy occupation occupationDerivative) :
    massiveDiracRegularizedStredaFermiSea data =
      ∫ energy in lowerEnergy..upperEnergy,
        occupation energy *
          regularizedStredaResidualSeaTraceKernel
            (hamiltonianOperator v m px py)
            (currentOperator .x e v) (currentOperator .y e v)
            energy broadening := by
  rfl

/-- Under the visible analytic hypotheses, the actual massive-Dirac traced Bastin energy integral
is exactly the repository's named Fermi-surface plus Fermi-sea contributions. -/
theorem massiveDiracRegularizedBastinEnergyIntegral_eq_surface_add_sea
    {e v m px py broadening lowerEnergy upperEnergy : ℝ}
    {occupation occupationDerivative : ℝ → ℂ}
    (data : MassiveDiracStredaAnalyticData
      e v m px py broadening lowerEnergy upperEnergy occupation occupationDerivative) :
    massiveDiracRegularizedBastinEnergyIntegral
        e v m px py broadening lowerEnergy upperEnergy occupation =
      massiveDiracRegularizedStredaFermiSurface data +
        massiveDiracRegularizedStredaFermiSea data := by
  unfold massiveDiracRegularizedBastinEnergyIntegral
  rw [← data.regularizedBastinEnergyIntegral_eq_traced]
  exact regularizedBastinEnergyIntegral_eq_surface_add_sea
    data.toRegularizedStredaIntegralData

/-- A sector with identically zero occupation derivative has no Fermi-surface contribution in the
repository's regularized Středa convention. This is the smooth finite-interval statement behind
the classification of a completely filled sector as a sea contribution; it does not model a
zero-temperature jump at a Fermi edge. -/
theorem massiveDiracRegularizedStredaFermiSurface_eq_zero_of_derivative_zero
    {e v m px py broadening lowerEnergy upperEnergy : ℝ}
    {occupation occupationDerivative : ℝ → ℂ}
    (data : MassiveDiracStredaAnalyticData
      e v m px py broadening lowerEnergy upperEnergy occupation occupationDerivative)
    (hzero : occupationDerivative = fun _ => 0) :
    massiveDiracRegularizedStredaFermiSurface data = 0 := by
  rw [massiveDiracRegularizedStredaFermiSurface_eq]
  simp [hzero]

/-- Consequently, a smooth completely filled sector is carried entirely by the residual Fermi-sea
term at fixed positive broadening. -/
theorem massiveDiracRegularizedBastinEnergyIntegral_eq_sea_of_derivative_zero
    {e v m px py broadening lowerEnergy upperEnergy : ℝ}
    {occupation occupationDerivative : ℝ → ℂ}
    (data : MassiveDiracStredaAnalyticData
      e v m px py broadening lowerEnergy upperEnergy occupation occupationDerivative)
    (hzero : occupationDerivative = fun _ => 0) :
    massiveDiracRegularizedBastinEnergyIntegral
        e v m px py broadening lowerEnergy upperEnergy occupation =
      massiveDiracRegularizedStredaFermiSea data := by
  rw [massiveDiracRegularizedBastinEnergyIntegral_eq_surface_add_sea data,
    massiveDiracRegularizedStredaFermiSurface_eq_zero_of_derivative_zero data hzero,
    zero_add]

end

end AnomalousHall.MassiveDirac
