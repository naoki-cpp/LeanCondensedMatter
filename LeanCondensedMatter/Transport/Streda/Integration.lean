import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option linter.style.header false

/-!
# Analytic boundary for the regularized Středa decomposition

The finite Kubo–Bastin theorem supplies an exact regularized response, but a Středa split requires
an additional energy representation and an integration-by-parts argument. This module records that
analytic boundary without pretending that the energy representation follows by definition.

For an occupation factor `f`, a surface primitive `P`, and a residual sea kernel `S`, write

```text
B = ∫ f(E) [P'(E) + S(E)] dE.
```

If `f` and `P` have the stated derivatives, the relevant products are interval integrable, and the
boundary term `[f P]ₐᵇ` vanishes, then

```text
B = -∫ f'(E) P(E) dE + ∫ f(E) S(E) dE.
```

The first term is named the regularized Fermi-surface contribution and the second the regularized
Fermi-sea contribution. A representation object additionally proves that a chosen response equals
`B`; canonical ordinary-trace Bastin energy representations are supplied downstream by the static
`Transport.Streda` trace layer. Only after such a representation is supplied does the response
inherit the split.

This module does not identify the sea term with a magnetic-field derivative of particle density or
magnetization. It also makes no zero-temperature distributional, zero-broadening, DC, disorder,
trace-per-unit-volume, or thermodynamic-limit claim.
-/

namespace QuantumTheory
namespace Transport

open MeasureTheory

noncomputable section

/-- Analytic data sufficient for one finite-interval regularized Středa integration by parts. -/
structure RegularizedStredaIntegralData where
  /-- Lower endpoint of the finite energy interval. -/
  lowerEnergy : ℝ
  /-- Upper endpoint of the finite energy interval. -/
  upperEnergy : ℝ
  /-- Complexified occupation factor. -/
  occupation : ℝ → ℂ
  /-- Derivative of the occupation factor. -/
  occupationDerivative : ℝ → ℂ
  /-- Primitive whose derivative contributes the surface part of the Bastin integrand. -/
  surfacePrimitive : ℝ → ℂ
  /-- Derivative of the surface primitive. -/
  surfacePrimitiveDerivative : ℝ → ℂ
  /-- Residual energy integrand defining the sea contribution. -/
  seaKernel : ℝ → ℂ
  occupation_continuous :
    ContinuousOn occupation (Set.uIcc lowerEnergy upperEnergy)
  surfacePrimitive_continuous :
    ContinuousOn surfacePrimitive (Set.uIcc lowerEnergy upperEnergy)
  occupation_hasDerivAt :
    ∀ energy ∈ Set.Ioo (min lowerEnergy upperEnergy) (max lowerEnergy upperEnergy),
      HasDerivAt occupation (occupationDerivative energy) energy
  surfacePrimitive_hasDerivAt :
    ∀ energy ∈ Set.Ioo (min lowerEnergy upperEnergy) (max lowerEnergy upperEnergy),
      HasDerivAt surfacePrimitive (surfacePrimitiveDerivative energy) energy
  occupationDerivative_intervalIntegrable :
    IntervalIntegrable occupationDerivative volume lowerEnergy upperEnergy
  surfacePrimitiveDerivative_intervalIntegrable :
    IntervalIntegrable surfacePrimitiveDerivative volume lowerEnergy upperEnergy
  surfaceProduct_intervalIntegrable :
    IntervalIntegrable
      (fun energy => occupation energy * surfacePrimitiveDerivative energy)
      volume lowerEnergy upperEnergy
  seaProduct_intervalIntegrable :
    IntervalIntegrable
      (fun energy => occupation energy * seaKernel energy)
      volume lowerEnergy upperEnergy
  /-- Explicit vanishing of the integration-by-parts boundary term. -/
  boundary_vanishes :
    occupation upperEnergy * surfacePrimitive upperEnergy -
      occupation lowerEnergy * surfacePrimitive lowerEnergy = 0

/-- The regularized Bastin energy integral before the Středa split. -/
noncomputable def regularizedBastinEnergyIntegral
    (data : RegularizedStredaIntegralData) : ℂ :=
  ∫ energy in data.lowerEnergy..data.upperEnergy,
    data.occupation energy *
      (data.surfacePrimitiveDerivative energy + data.seaKernel energy)

/-- Named regularized Fermi-surface contribution. -/
noncomputable def regularizedStredaFermiSurface
    (data : RegularizedStredaIntegralData) : ℂ :=
  -(∫ energy in data.lowerEnergy..data.upperEnergy,
      data.occupationDerivative energy * data.surfacePrimitive energy)

/-- Named regularized Fermi-sea contribution. -/
noncomputable def regularizedStredaFermiSea
    (data : RegularizedStredaIntegralData) : ℂ :=
  ∫ energy in data.lowerEnergy..data.upperEnergy,
    data.occupation energy * data.seaKernel energy

/-- Integration by parts gives the regularized surface/sea decomposition on the finite energy
interval. Every derivative, integrability, and boundary hypothesis is stored in `data`. -/
theorem regularizedBastinEnergyIntegral_eq_surface_add_sea
    (data : RegularizedStredaIntegralData) :
    regularizedBastinEnergyIntegral data =
      regularizedStredaFermiSurface data + regularizedStredaFermiSea data := by
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    data.occupation_continuous data.surfacePrimitive_continuous
    data.occupation_hasDerivAt data.surfacePrimitive_hasDerivAt
    data.occupationDerivative_intervalIntegrable
    data.surfacePrimitiveDerivative_intervalIntegrable
  have hsurface :
      (∫ energy in data.lowerEnergy..data.upperEnergy,
          data.occupation energy * data.surfacePrimitiveDerivative energy) =
        -(∫ energy in data.lowerEnergy..data.upperEnergy,
          data.occupationDerivative energy * data.surfacePrimitive energy) := by
    rw [data.boundary_vanishes] at hparts
    simpa using hparts
  unfold regularizedBastinEnergyIntegral regularizedStredaFermiSurface
    regularizedStredaFermiSea
  simp_rw [mul_add]
  rw [intervalIntegral.integral_add
    data.surfaceProduct_intervalIntegrable data.seaProduct_intervalIntegrable, hsurface]

/-- A proof that a chosen regularized response has the energy-integral representation required by
the Středa integration boundary. -/
structure RegularizedStredaRepresentation (response : ℂ)
    extends RegularizedStredaIntegralData where
  response_eq_energyIntegral :
    response = regularizedBastinEnergyIntegral toRegularizedStredaIntegralData

/-- Any response equipped with the explicit energy representation and analytic hypotheses splits
as its named regularized Fermi-surface and Fermi-sea contributions. -/
theorem RegularizedStredaRepresentation.response_eq_surface_add_sea
    {response : ℂ} (representation : RegularizedStredaRepresentation response) :
    response =
      regularizedStredaFermiSurface representation.toRegularizedStredaIntegralData +
        regularizedStredaFermiSea representation.toRegularizedStredaIntegralData := by
  calc
    response = regularizedBastinEnergyIntegral
        representation.toRegularizedStredaIntegralData :=
      representation.response_eq_energyIntegral
    _ = regularizedStredaFermiSurface representation.toRegularizedStredaIntegralData +
        regularizedStredaFermiSea representation.toRegularizedStredaIntegralData :=
      regularizedBastinEnergyIntegral_eq_surface_add_sea
        representation.toRegularizedStredaIntegralData

end
end Transport
end QuantumTheory
