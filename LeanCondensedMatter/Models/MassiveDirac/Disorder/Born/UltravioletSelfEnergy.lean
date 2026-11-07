import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.Denominator
import LeanCondensedMatter.Models.MassiveDirac.Disorder.FiniteBroadeningBornPropagator
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Ultraviolet behavior of the continuum Born self-energy

The common radial Born denominator has an existing logarithmic ultraviolet
divergence of its real part. This file transports that analytic result to
the actual channel-wise continuum Born self-energy coefficients, keeping
the physical disorder and momentum-measure normalization explicit.

An ultraviolet limit of the *fixed spectral center* Fourier transform does
not imply an unrenormalized infinite-cutoff limit for the corresponding
Born-Dyson Green function: its effective spectral energy and mass inherit
the ultraviolet self-energy shift.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport
open Filter

/-- Both surviving Born channels use the same finite-cutoff denominator
integral; the only channel dependence is the fixed complex numerator.
The continuum disorder and momentum-measure factor occurs exactly once. -/
theorem finiteCutoffContinuumBornSelfEnergyCoefficient_eq_denominatorIntegral
    (channel : BornSelfEnergyChannel) (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornSelfEnergyCoefficient channel side
      v m probeEnergy broadening disorderStrength hbar pMax =
    ((disorderStrength * fullAngleMomentumMeasurePrefactor hbar : ℝ) : ℂ) *
      bornSelfEnergyChannelWeight channel side m probeEnergy broadening *
      finiteCutoffContinuumBornDenominatorIntegral
        side v m probeEnergy broadening pMax := by
  unfold finiteCutoffContinuumBornSelfEnergyCoefficient
    finiteCutoffContinuumBornSelfEnergyCoefficientOfRegulator
  rw [show finiteCutoffContinuumBornIntegralOfRegulator channel v m probeEnergy
      (side.regulator broadening) pMax =
      bornSelfEnergyChannelWeight channel side m probeEnergy broadening *
        finiteCutoffContinuumBornDenominatorIntegral
          side v m probeEnergy broadening pMax from by
    simpa only [finiteCutoffContinuumBornIntegral,
      finiteCutoffContinuumBornSelfEnergyCoefficient,
      bornSelfEnergyChannelWeight, finiteCutoffContinuumBornDenominatorIntegral]
      using finiteCutoffContinuumBornIntegral_eq_weight_mul_denominatorIntegral
        channel side v m probeEnergy broadening pMax]
  ring

/-- The real part of each channel coefficient, divided by its *nonzero*
physical disorder/measure/numerator factor, tends to negative infinity as
the momentum cutoff increases. This is the sharp obstruction to taking
an unrenormalized ultraviolet limit at fixed nonzero Born coupling. -/
theorem tendsto_finiteCutoffContinuumBornSelfEnergyCoefficient_normalized_re_atBot
    (channel : BornSelfEnergyChannel) (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar : ℝ)
    (hv : v ≠ 0) (henergy : probeEnergy ≠ 0) (hbroadening : broadening ≠ 0)
    (hfactor :
      ((disorderStrength * fullAngleMomentumMeasurePrefactor hbar : ℝ) : ℂ) *
        bornSelfEnergyChannelWeight channel side m probeEnergy broadening ≠ 0) :
    Tendsto
      (fun pMax : ℝ =>
        ((finiteCutoffContinuumBornSelfEnergyCoefficient channel side
          v m probeEnergy broadening disorderStrength hbar pMax /
          (((disorderStrength * fullAngleMomentumMeasurePrefactor hbar : ℝ) : ℂ) *
            bornSelfEnergyChannelWeight channel side m probeEnergy broadening)).re))
      atTop atBot := by
  have hJ :=
    tendsto_finiteCutoffContinuumBornDenominatorIntegralOfRegulator_re_atTop
      v m probeEnergy (side.regulator broadening)
      hv henergy (side.regulator_ne_zero hbroadening)
  have hident (pMax : ℝ) :
      finiteCutoffContinuumBornSelfEnergyCoefficient channel side
          v m probeEnergy broadening disorderStrength hbar pMax /
          (((disorderStrength * fullAngleMomentumMeasurePrefactor hbar : ℝ) : ℂ) *
            bornSelfEnergyChannelWeight channel side m probeEnergy broadening) =
      finiteCutoffContinuumBornDenominatorIntegral
        side v m probeEnergy broadening pMax := by
    rw [finiteCutoffContinuumBornSelfEnergyCoefficient_eq_denominatorIntegral]
    apply (div_eq_iff hfactor).2
    ring
  convert hJ using 1
  funext pMax
  rw [hident]
  rfl

/-- The scalar Born shift of the Dyson effective energy inherits the
same divergent normalized real projection as the physical self-energy. -/
theorem tendsto_finiteCutoffContinuumBornEffectiveEnergy_shift_normalized_re_atBot
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar : ℝ)
    (hv : v ≠ 0) (henergy : probeEnergy ≠ 0) (hbroadening : broadening ≠ 0)
    (hfactor :
      ((disorderStrength * fullAngleMomentumMeasurePrefactor hbar : ℝ) : ℂ) *
        bornSelfEnergyChannelWeight .scalar side m probeEnergy broadening ≠ 0) :
    Tendsto
      (fun pMax : ℝ =>
        ((spectralParameter side probeEnergy broadening -
          finiteCutoffContinuumBornEffectiveEnergy side
            v m probeEnergy broadening disorderStrength hbar pMax) /
          (((disorderStrength * fullAngleMomentumMeasurePrefactor hbar : ℝ) : ℂ) *
            bornSelfEnergyChannelWeight .scalar side m probeEnergy broadening)).re)
      atTop atBot := by
  have h :=
    tendsto_finiteCutoffContinuumBornSelfEnergyCoefficient_normalized_re_atBot
      .scalar side v m probeEnergy broadening disorderStrength hbar
      hv henergy hbroadening hfactor
  convert h using 1
  funext pMax
  congr 1
  congr 1
  unfold finiteCutoffContinuumBornEffectiveEnergy
  ring

/-- The mass channel shifts the Dyson effective Dirac mass by the same
ultraviolet-divergent Born coefficient, with the channel factor removed. -/
theorem tendsto_finiteCutoffContinuumBornEffectiveMass_shift_normalized_re_atBot
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar : ℝ)
    (hv : v ≠ 0) (henergy : probeEnergy ≠ 0) (hbroadening : broadening ≠ 0)
    (hfactor :
      ((disorderStrength * fullAngleMomentumMeasurePrefactor hbar : ℝ) : ℂ) *
        bornSelfEnergyChannelWeight .z side m probeEnergy broadening ≠ 0) :
    Tendsto
      (fun pMax : ℝ =>
        ((finiteCutoffContinuumBornEffectiveMass side
            v m probeEnergy broadening disorderStrength hbar pMax - (m : ℂ)) /
          (((disorderStrength * fullAngleMomentumMeasurePrefactor hbar : ℝ) : ℂ) *
            bornSelfEnergyChannelWeight .z side m probeEnergy broadening)).re)
      atTop atBot := by
  have h :=
    tendsto_finiteCutoffContinuumBornSelfEnergyCoefficient_normalized_re_atBot
      .z side v m probeEnergy broadening disorderStrength hbar
      hv henergy hbroadening hfactor
  convert h using 1
  funext pMax
  congr 1
  congr 1
  unfold finiteCutoffContinuumBornEffectiveMass
  ring

end

end QuantumTheory.Models.MassiveDirac
