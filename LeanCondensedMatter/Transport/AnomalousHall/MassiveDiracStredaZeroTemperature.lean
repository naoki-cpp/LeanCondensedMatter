import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracStredaIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Zero-temperature finite-window Středa split for the massive Dirac model

At zero temperature the occupied energy interval can be treated directly, without replacing the
occupation derivative by a delta distribution.  On a finite interval from `lowerEnergy` to the
Fermi energy, the fixed-positive-broadening Bastin kernel satisfies

```text
∫ (P'(E) + S(E)) dE
  = P(ε_F) - P(lowerEnergy) + ∫ S(E) dE.
```

Here `P` is the repository's regularized Středa surface primitive and `S` the residual sea kernel.
This gives an exact zero-temperature finite-window surface/sea split using only ordinary interval
integration and the fundamental theorem of calculus.

The lower-endpoint primitive is kept explicit.  Removing that boundary, taking the positive-
broadening limit, integrating over momentum, and identifying the resulting clean surface/sea terms
remain downstream steps.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open MeasureTheory QuantumTheory.Transport

/-- Zero-temperature occupied finite-window Bastin energy integral for one momentum fiber. -/
noncomputable def massiveDiracZeroTemperatureBastinEnergyIntegral
    (e v m px py broadening lowerEnergy fermiEnergy : ℝ) : ℂ :=
  ∫ energy in lowerEnergy..fermiEnergy,
    regularizedBastinTraceIntegrand
      (hamiltonianOperator v m px py)
      (currentXOperator e v) (currentYOperator e v)
      energy broadening

/-- Exact finite-window zero-temperature Fermi-surface term.  The lower-energy boundary remains
visible until a later improper-energy limit proves that it vanishes. -/
noncomputable def massiveDiracZeroTemperatureStredaFermiSurface
    (e v m px py broadening lowerEnergy fermiEnergy : ℝ) : ℂ :=
  regularizedStredaSurfacePrimitiveTrace
      (hamiltonianOperator v m px py)
      (currentXOperator e v) (currentYOperator e v)
      fermiEnergy broadening -
    regularizedStredaSurfacePrimitiveTrace
      (hamiltonianOperator v m px py)
      (currentXOperator e v) (currentYOperator e v)
      lowerEnergy broadening

/-- Exact finite-window zero-temperature Fermi-sea term. -/
noncomputable def massiveDiracZeroTemperatureStredaFermiSea
    (e v m px py broadening lowerEnergy fermiEnergy : ℝ) : ℂ :=
  ∫ energy in lowerEnergy..fermiEnergy,
    regularizedStredaResidualSeaTraceKernel
      (hamiltonianOperator v m px py)
      (currentXOperator e v) (currentYOperator e v)
      energy broadening

/-- At fixed positive broadening, the occupied zero-temperature Bastin energy integral is exactly
its Fermi-edge surface primitive difference plus the occupied residual sea integral.

This is the ordinary-function replacement for the informal zero-temperature shortcut
`-f'(E) = δ(E - ε_F)`: no distributional derivative is used. -/
theorem massiveDiracZeroTemperatureBastinEnergyIntegral_eq_surface_add_sea
    (e v m px py broadening lowerEnergy fermiEnergy : ℝ)
    (hbroadening : 0 < broadening) (hlowerFermi : lowerEnergy ≤ fermiEnergy)
    (hsurfaceIntegrable :
      IntervalIntegrable
        (fun energy => regularizedStredaSurfacePrimitiveTraceDerivative
          (hamiltonianOperator v m px py)
          (currentXOperator e v) (currentYOperator e v)
          energy broadening)
        volume lowerEnergy fermiEnergy)
    (hseaIntegrable :
      IntervalIntegrable
        (fun energy => regularizedStredaResidualSeaTraceKernel
          (hamiltonianOperator v m px py)
          (currentXOperator e v) (currentYOperator e v)
          energy broadening)
        volume lowerEnergy fermiEnergy) :
    massiveDiracZeroTemperatureBastinEnergyIntegral
        e v m px py broadening lowerEnergy fermiEnergy =
      massiveDiracZeroTemperatureStredaFermiSurface
          e v m px py broadening lowerEnergy fermiEnergy +
        massiveDiracZeroTemperatureStredaFermiSea
          e v m px py broadening lowerEnergy fermiEnergy := by
  let primitive : ℝ → ℂ := fun energy =>
    regularizedStredaSurfacePrimitiveTrace
      (hamiltonianOperator v m px py)
      (currentXOperator e v) (currentYOperator e v)
      energy broadening
  let primitiveDerivative : ℝ → ℂ := fun energy =>
    regularizedStredaSurfacePrimitiveTraceDerivative
      (hamiltonianOperator v m px py)
      (currentXOperator e v) (currentYOperator e v)
      energy broadening
  have hprimitiveContinuous : ContinuousOn primitive (Set.Icc lowerEnergy fermiEnergy) := by
    intro energy _
    exact
      (hasDerivAt_regularizedStredaSurfacePrimitiveTrace
        (hamiltonianOperator v m px py)
        (hamiltonianOperator_isSelfAdjoint v m px py)
        (currentXOperator e v) (currentYOperator e v)
        energy broadening hbroadening).continuousAt.continuousWithinAt
  have hprimitiveDeriv :
      ∀ energy ∈ Set.Ioo lowerEnergy fermiEnergy,
        HasDerivAt primitive (primitiveDerivative energy) energy := by
    intro energy _
    exact hasDerivAt_regularizedStredaSurfacePrimitiveTrace
      (hamiltonianOperator v m px py)
      (hamiltonianOperator_isSelfAdjoint v m px py)
      (currentXOperator e v) (currentYOperator e v)
      energy broadening hbroadening
  have hsurfaceFTC :
      (∫ energy in lowerEnergy..fermiEnergy, primitiveDerivative energy) =
        primitive fermiEnergy - primitive lowerEnergy := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      hlowerFermi hprimitiveContinuous hprimitiveDeriv hsurfaceIntegrable
  have hkernel :
      (fun energy => regularizedBastinTraceIntegrand
        (hamiltonianOperator v m px py)
        (currentXOperator e v) (currentYOperator e v)
        energy broadening) =
      (fun energy => primitiveDerivative energy +
        regularizedStredaResidualSeaTraceKernel
          (hamiltonianOperator v m px py)
          (currentXOperator e v) (currentYOperator e v)
          energy broadening) := by
    funext energy
    exact regularizedBastinTraceIntegrand_eq_streda
      e v m px py energy broadening
  unfold massiveDiracZeroTemperatureBastinEnergyIntegral
    massiveDiracZeroTemperatureStredaFermiSurface
    massiveDiracZeroTemperatureStredaFermiSea
  rw [hkernel]
  rw [intervalIntegral.integral_add hsurfaceIntegrable hseaIntegrable]
  change
    (∫ energy in lowerEnergy..fermiEnergy, primitiveDerivative energy) +
        (∫ energy in lowerEnergy..fermiEnergy,
          regularizedStredaResidualSeaTraceKernel
            (hamiltonianOperator v m px py)
            (currentXOperator e v) (currentYOperator e v)
            energy broadening) =
      (primitive fermiEnergy - primitive lowerEnergy) +
        (∫ energy in lowerEnergy..fermiEnergy,
          regularizedStredaResidualSeaTraceKernel
            (hamiltonianOperator v m px py)
            (currentXOperator e v) (currentYOperator e v)
            energy broadening)
  rw [hsurfaceFTC]

/-- If the lower-energy surface primitive vanishes, the zero-temperature Fermi-surface term is
literally the regularized Středa primitive evaluated at the Fermi energy. -/
theorem massiveDiracZeroTemperatureStredaFermiSurface_eq_atFermi_of_lower_eq_zero
    (e v m px py broadening lowerEnergy fermiEnergy : ℝ)
    (hlower :
      regularizedStredaSurfacePrimitiveTrace
        (hamiltonianOperator v m px py)
        (currentXOperator e v) (currentYOperator e v)
        lowerEnergy broadening = 0) :
    massiveDiracZeroTemperatureStredaFermiSurface
        e v m px py broadening lowerEnergy fermiEnergy =
      regularizedStredaSurfacePrimitiveTrace
        (hamiltonianOperator v m px py)
        (currentXOperator e v) (currentYOperator e v)
        fermiEnergy broadening := by
  simp [massiveDiracZeroTemperatureStredaFermiSurface, hlower]

end

end AnomalousHall.MassiveDirac
