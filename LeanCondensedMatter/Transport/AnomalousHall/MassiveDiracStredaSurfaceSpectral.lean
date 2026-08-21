import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracStredaZeroTemperatureBoundary
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinBands
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Massive-Dirac spectral decomposition of the Středa surface primitive

The zero-temperature Středa development has reduced the finite-energy-window surface term to the
single Fermi-edge primitive at fixed positive broadening.  Before taking the clean limit, this file
expands that primitive in the same gauge-free two-band projector basis used by the Bastin chain.

For an ordered pair `(source,target)`, the surface coefficient is

```text
-1/2 * (r_source * (r_target - a_target) * Tr(jx P_source jy P_target)
      - a_source * (r_target - a_target) * Tr(jy P_source jx P_target)).
```

The exact finite-broadening primitive is the sum of the four ordered band pairs.  Diagonal and
interband sectors are named separately so the following slice can isolate the Fermi-shell
Lorentzian contribution before the radial momentum integral.  No broadening limit or momentum
integration is taken here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Contribution of one ordered band pair to the regularized Středa surface primitive trace. -/
noncomputable def stredaSurfaceBandPairContribution
    (source target : Band) (e v m px py probeEnergy broadening : ℝ) : ℂ :=
  let r := projectorResolventCoefficient
    (retardedSpectralParameter probeEnergy broadening) source v m px py
  let a := projectorResolventCoefficient
    (advancedSpectralParameter probeEnergy broadening) source v m px py
  let d := spectralDifferenceCoefficient target v m px py probeEnergy broadening
  (-(1 / 2 : ℂ)) *
    (r * d * bastinXYBandBlockTrace source target e v m px py -
      a * d * bastinYXBandBlockTrace source target e v m px py)

/-- Intraband part of the finite-broadening Středa surface primitive. -/
noncomputable def diagonalStredaSurfaceTraceContribution
    (e v m px py probeEnergy broadening : ℝ) : ℂ :=
  stredaSurfaceBandPairContribution .lower .lower e v m px py probeEnergy broadening +
    stredaSurfaceBandPairContribution .upper .upper e v m px py probeEnergy broadening

/-- Interband part of the finite-broadening Středa surface primitive. -/
noncomputable def interbandStredaSurfaceTraceContribution
    (e v m px py probeEnergy broadening : ℝ) : ℂ :=
  stredaSurfaceBandPairContribution .lower .upper e v m px py probeEnergy broadening +
    stredaSurfaceBandPairContribution .upper .lower e v m px py probeEnergy broadening

/-- Exact four-band projector expansion of the massive-Dirac Středa surface primitive at fixed
positive broadening. -/
theorem regularizedStredaSurfacePrimitiveTrace_eq_four_band_blocks
    (e v m px py probeEnergy broadening : ℝ)
    (hE : energy v m px py ≠ 0) (hbroadening : 0 < broadening) :
    regularizedStredaSurfacePrimitiveTrace
        (hamiltonianOperator v m px py)
        (currentXOperator e v) (currentYOperator e v)
        probeEnergy broadening =
      stredaSurfaceBandPairContribution .lower .lower
          e v m px py probeEnergy broadening +
      stredaSurfaceBandPairContribution .lower .upper
          e v m px py probeEnergy broadening +
      stredaSurfaceBandPairContribution .upper .lower
          e v m px py probeEnergy broadening +
      stredaSurfaceBandPairContribution .upper .upper
          e v m px py probeEnergy broadening := by
  unfold regularizedStredaSurfacePrimitiveTrace regularizedStredaSurfacePrimitiveOperator
    smrckaStredaSurfaceFactor retardedAdvancedResolventDifference
  rw [retardedResolvent_eq_projectorResolvent
    v m px py probeEnergy broadening hE hbroadening]
  rw [advancedResolvent_eq_projectorResolvent
    v m px py probeEnergy broadening hE hbroadening]
  rw [projectorResolvent_eq_coefficients
    (retardedSpectralParameter probeEnergy broadening) v m px py]
  rw [projectorResolvent_eq_coefficients
    (advancedSpectralParameter probeEnergy broadening) v m px py]
  unfold stredaSurfaceBandPairContribution spectralDifferenceCoefficient
    bastinXYBandBlockTrace bastinYXBandBlockTrace
  simp only [add_mul, sub_mul, mul_add, mul_sub, mul_smul_comm, smul_mul_assoc]
  simp only [map_add, map_sub, map_smul]
  ring_nf

/-- Exact finite-broadening separation of the Středa surface primitive into diagonal and interband
sectors. -/
theorem regularizedStredaSurfacePrimitiveTrace_eq_diagonal_add_interband
    (e v m px py probeEnergy broadening : ℝ)
    (hE : energy v m px py ≠ 0) (hbroadening : 0 < broadening) :
    regularizedStredaSurfacePrimitiveTrace
        (hamiltonianOperator v m px py)
        (currentXOperator e v) (currentYOperator e v)
        probeEnergy broadening =
      diagonalStredaSurfaceTraceContribution
          e v m px py probeEnergy broadening +
        interbandStredaSurfaceTraceContribution
          e v m px py probeEnergy broadening := by
  rw [regularizedStredaSurfacePrimitiveTrace_eq_four_band_blocks
    e v m px py probeEnergy broadening hE hbroadening]
  unfold diagonalStredaSurfaceTraceContribution interbandStredaSurfaceTraceContribution
  ring

end

end AnomalousHall.MassiveDirac
