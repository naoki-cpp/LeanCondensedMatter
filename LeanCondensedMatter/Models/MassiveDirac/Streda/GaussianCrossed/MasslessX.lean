import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.UltravioletSelfEnergy
import LeanCondensedMatter.Models.MassiveDirac.Streda.GaussianCrossed.GreenGeneratorMinors
import LeanCondensedMatter.Models.MassiveDirac.Streda.GaussianCrossed.RadialCoefficients

set_option linter.style.header false

/-!
# Exact vanishing of the regulated crossed X Hall kernel at zero Dirac mass

This verifies the time-reversal-symmetric massless boundary of the *actual*
finite-broadening, finite-momentum-cutoff Born-Dyson X topology. The proof
uses the physical Born self-energy, physical crossed-current Fourier kernels
and scalar-generator factorization of the Green minors. It is valid at
nonnegative finite disorder strength, not just at vanishing disorder.

This special case is not the massive-metal X integral evaluation: the
nonzero-mass weak-disorder/zero-broadening and real-space limits remain open.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- A finite-cutoff massless Dirac propagator has no z-Pauli component
for either causal side, even with scalar Born self-energy. -/
@[simp] theorem finiteCutoffContinuumBornDysonPauliCoefficient_z_zero_mass
    (side : SpectralSide)
    (v px py probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonPauliCoefficient .z
      side v 0 px py probeEnergy broadening disorderStrength hbar pMax = 0 := by
  simp [finiteCutoffContinuumBornDysonPauliCoefficient,
    InternalSpace.pauliAxisComponent]

/-- The source-x current's transverse Pauli-y radial kernel vanishes at
zero mass. Its numerator contains a z-Pauli Green coefficient. -/
@[simp] theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliKernel_y_zero_mass
    (v probeEnergy broadening disorderStrength hbar pMax radius p : ℝ) :
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliKernel
      .y 0 v 0 probeEnergy broadening disorderStrength hbar pMax radius p = 0 := by
  simp [finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliKernel]

/-- The source-x current's z-Pauli radial kernel likewise vanishes at
zero Dirac mass. -/
@[simp] theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliKernel_z_zero_mass
    (v probeEnergy broadening disorderStrength hbar pMax radius p : ℝ) :
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliKernel
      .z 0 v 0 probeEnergy broadening disorderStrength hbar pMax radius p = 0 := by
  simp [finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliKernel]

/-- The two vanishing pointwise current kernels also vanish *after* the
full finite radial momentum integration. This uses finite-broadening
continuity rather than exchanging any cutoff limit with integration. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrent_yz_zero_mass
    (v probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
      .y 0 v 0 probeEnergy broadening disorderStrength hbar pMax radius = 0 ∧
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
      .z 0 v 0 probeEnergy broadening disorderStrength hbar pMax radius = 0 := by
  constructor
  · rw [finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_eq_radialKernel_integral
      .y 0 v 0 probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax]
    simp
  · rw [finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_eq_radialKernel_integral
      .z 0 v 0 probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax]
    simp

/-- All three minors in the generator-factored finite-radius X amplitude
vanish at zero Dirac mass. In particular the massless X kernel is zero
even when the physical Gaussian disorder correlator is positive. -/
@[simp] theorem finiteCutoffContinuumBornDysonGaussianCrossedXGeneratorRadialAmplitude_zero_mass
    (v probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    finiteCutoffContinuumBornDysonGaussianCrossedXGeneratorRadialAmplitude
      v 0 probeEnergy broadening disorderStrength hbar pMax radius = 0 := by
  obtain ⟨hy, hz⟩ :=
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrent_yz_zero_mass
      v probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax
  unfold finiteCutoffContinuumBornDysonGaussianCrossedXGeneratorRadialAmplitude
  dsimp only [finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient] at hy hz
  dsimp only
  simp only [finiteCutoffContinuumBornEffectiveMass_zero_mass,
    zero_mul, mul_zero, sub_self, sub_zero, add_zero]
  rw [hy, hz]
  ring

end

end QuantumTheory.Models.MassiveDirac
