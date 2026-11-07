import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.Denominator
import LeanCondensedMatter.Models.MassiveDirac.Disorder.FiniteBroadeningBornPropagator
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
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

/-- The scalar and z components of the finite-cutoff Born self-energy
have exactly the same radial logarithm. Their numerators are therefore
proportional, even before taking any ultraviolet or regulator limit. -/
theorem finiteCutoffContinuumBornSelfEnergyCoefficient_scalar_z_balance
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    (m : ℂ) *
        finiteCutoffContinuumBornSelfEnergyCoefficient .scalar
          side v m probeEnergy broadening disorderStrength hbar pMax =
      spectralParameter side probeEnergy broadening *
        finiteCutoffContinuumBornSelfEnergyCoefficient .z
          side v m probeEnergy broadening disorderStrength hbar pMax := by
  rw [finiteCutoffContinuumBornSelfEnergyCoefficient_eq_denominatorIntegral,
    finiteCutoffContinuumBornSelfEnergyCoefficient_eq_denominatorIntegral]
  simp only [bornSelfEnergyChannelWeight, bornSelfEnergyChannelWeightOfRegulator,
    spectralParameter]
  ring

/-- Although the two Born-Dyson spectral parameters may each acquire
a logarithmically divergent correction, this combination is exactly
cutoff-independent. It is an algebraic identity, not a renormalized
infinite-cutoff Green function or a Ward identity. -/
theorem finiteCutoffContinuumBornEffectiveEnergyMass_cutoff_invariant
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    (m : ℂ) *
        finiteCutoffContinuumBornEffectiveEnergy
          side v m probeEnergy broadening disorderStrength hbar pMax +
      spectralParameter side probeEnergy broadening *
        finiteCutoffContinuumBornEffectiveMass
          side v m probeEnergy broadening disorderStrength hbar pMax =
      2 * (m : ℂ) * spectralParameter side probeEnergy broadening := by
  have hbalance := finiteCutoffContinuumBornSelfEnergyCoefficient_scalar_z_balance
    side v m probeEnergy broadening disorderStrength hbar pMax
  unfold finiteCutoffContinuumBornEffectiveEnergy
    finiteCutoffContinuumBornEffectiveMass
  linear_combination -hbalance

/-- The scalar Born-channel numerator cannot vanish at nonzero
external broadening, for either causal spectral side. -/
private theorem bornSelfEnergyScalarWeight_ne_zero
    (side : SpectralSide) (m probeEnergy broadening : ℝ)
    (hbroadening : broadening ≠ 0) :
    bornSelfEnergyChannelWeight .scalar side m probeEnergy broadening ≠ 0 := by
  intro hz
  have him := congrArg Complex.im hz
  have hzero : side.regulator broadening = 0 := by
    simpa [bornSelfEnergyChannelWeight, bornSelfEnergyChannelWeightOfRegulator,
      spectralParameterOfRegulator_im] using him
  exact side.regulator_ne_zero hbroadening hzero

/-- In the physical regime of positive disorder strength and Planck
constant, the scalar Born self-energy has an ultraviolet-divergent
normalized real projection without any additional prefactor hypothesis.
The nonzero broadening guarantees its scalar spectral numerator is nonzero. -/
theorem tendsto_finiteCutoffContinuumBornSelfEnergyCoefficient_scalar_normalized_re_atBot
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar : ℝ)
    (hv : v ≠ 0) (henergy : probeEnergy ≠ 0)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 < disorderStrength)
    (hhbar : 0 < hbar) :
    Tendsto
      (fun pMax : ℝ =>
        ((finiteCutoffContinuumBornSelfEnergyCoefficient .scalar side
          v m probeEnergy broadening disorderStrength hbar pMax /
          (((disorderStrength * fullAngleMomentumMeasurePrefactor hbar : ℝ) : ℂ) *
            bornSelfEnergyChannelWeight .scalar side m probeEnergy broadening)).re))
      atTop atBot := by
  have hmeasure : 0 < fullAngleMomentumMeasurePrefactor hbar := by
    unfold fullAngleMomentumMeasurePrefactor momentumMeasurePrefactor
    positivity
  have hfactor :
      ((disorderStrength * fullAngleMomentumMeasurePrefactor hbar : ℝ) : ℂ) *
        bornSelfEnergyChannelWeight .scalar side m probeEnergy broadening ≠ 0 :=
    mul_ne_zero
      (Complex.ofReal_ne_zero.mpr (mul_pos hdisorder hmeasure).ne')
      (bornSelfEnergyScalarWeight_ne_zero side m probeEnergy broadening hbroadening)
  exact tendsto_finiteCutoffContinuumBornSelfEnergyCoefficient_normalized_re_atBot
    .scalar side v m probeEnergy broadening disorderStrength hbar
    hv henergy hbroadening hfactor

/-- The z-Pauli Born coefficient also has a divergent normalized real
projection when the bare mass is nonzero. -/
theorem tendsto_finiteCutoffContinuumBornSelfEnergyCoefficient_z_normalized_re_atBot
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar : ℝ)
    (hv : v ≠ 0) (hm : m ≠ 0) (henergy : probeEnergy ≠ 0)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 < disorderStrength)
    (hhbar : 0 < hbar) :
    Tendsto
      (fun pMax : ℝ =>
        ((finiteCutoffContinuumBornSelfEnergyCoefficient .z side
          v m probeEnergy broadening disorderStrength hbar pMax /
          (((disorderStrength * fullAngleMomentumMeasurePrefactor hbar : ℝ) : ℂ) *
            bornSelfEnergyChannelWeight .z side m probeEnergy broadening)).re))
      atTop atBot := by
  have hmeasure : 0 < fullAngleMomentumMeasurePrefactor hbar := by
    unfold fullAngleMomentumMeasurePrefactor momentumMeasurePrefactor
    positivity
  have hweight :
      bornSelfEnergyChannelWeight .z side m probeEnergy broadening ≠ 0 := by
    simpa [bornSelfEnergyChannelWeight,
      bornSelfEnergyChannelWeightOfRegulator] using
      (Complex.ofReal_ne_zero.mpr hm)
  have hfactor :
      ((disorderStrength * fullAngleMomentumMeasurePrefactor hbar : ℝ) : ℂ) *
        bornSelfEnergyChannelWeight .z side m probeEnergy broadening ≠ 0 :=
    mul_ne_zero
      (Complex.ofReal_ne_zero.mpr (mul_pos hdisorder hmeasure).ne')
      hweight
  exact tendsto_finiteCutoffContinuumBornSelfEnergyCoefficient_normalized_re_atBot
    .z side v m probeEnergy broadening disorderStrength hbar
    hv henergy hbroadening hfactor

/-- At fixed nonzero normalization, no complex finite ultraviolet limit
exists for a channel's continuum Born self-energy coefficient. The proof
reduces a hypothetical finite complex limit to a finite limit of the
normalized real projection, contradicting its proved `atBot` behavior. -/
theorem finiteCutoffContinuumBornSelfEnergyCoefficient_no_finite_uv_limit
    (channel : BornSelfEnergyChannel) (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar : ℝ)
    (hv : v ≠ 0) (henergy : probeEnergy ≠ 0) (hbroadening : broadening ≠ 0)
    (hfactor :
      ((disorderStrength * fullAngleMomentumMeasurePrefactor hbar : ℝ) : ℂ) *
        bornSelfEnergyChannelWeight channel side m probeEnergy broadening ≠ 0) :
    ¬ ∃ limit : ℂ, Tendsto
      (fun pMax : ℝ =>
        finiteCutoffContinuumBornSelfEnergyCoefficient channel side
          v m probeEnergy broadening disorderStrength hbar pMax)
      atTop (nhds limit) := by
  let factor : ℂ :=
    ((disorderStrength * fullAngleMomentumMeasurePrefactor hbar : ℝ) : ℂ) *
      bornSelfEnergyChannelWeight channel side m probeEnergy broadening
  let sigma : ℝ → ℂ := fun pMax =>
    finiteCutoffContinuumBornSelfEnergyCoefficient channel side
      v m probeEnergy broadening disorderStrength hbar pMax
  have hdiv : Tendsto
      (fun pMax : ℝ => (sigma pMax / factor).re) atTop atBot :=
    tendsto_finiteCutoffContinuumBornSelfEnergyCoefficient_normalized_re_atBot
      channel side v m probeEnergy broadening disorderStrength hbar
      hv henergy hbroadening hfactor
  rintro ⟨limit, hlimit⟩
  have hfinite : Tendsto
      (fun pMax : ℝ => (sigma pMax / factor).re)
      atTop (nhds (limit / factor).re) := by
    exact (Complex.continuous_re.tendsto (limit / factor)).comp
      (hlimit.div_const factor)
  let a : ℝ := (limit / factor).re
  have hupper : ∀ᶠ pMax in atTop,
      (sigma pMax / factor).re ≤ a - 2 :=
    hdiv.eventually (Filter.eventually_le_atBot (a - 2))
  have hlower : ∀ᶠ pMax in atTop,
      a - 1 < (sigma pMax / factor).re :=
    hfinite.eventually (Ioi_mem_nhds (by linarith : a - 1 < a))
  obtain ⟨pMax, hpUpper, hpLower⟩ := (hupper.and hlower).exists
  linarith

end

end QuantumTheory.Models.MassiveDirac
