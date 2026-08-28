import LeanCondensedMatter.Transport.Analysis.SingleParticleLifetime
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.SelfEnergyBroadeningLimit
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Model.BandProjection
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Model.Occupation
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Band-projected continuum Born decay width and single-particle lifetime

This file makes the microscopic bridge from the existing finite-cutoff continuum Born self-energy
to a single-particle lifetime for the metallic upper band.  The retarded Born self-energy has only
identity and `σ_z` channels after angular reduction.  Those two channels are projected onto a clean
massive-Dirac band using the gauge-independent spectral projector, and the upper band is then put on
the occupation-derived Fermi circle.

At finite Green-function broadening `η`, the regularized decay half-width is

```text
Γ_q(η) = -Im Σ⁺ᴿ(ε_F; η).
```

The existing fixed-cutoff `η → 0+` self-energy limits then give

```text
Γ_q = disorderStrength / (4 ℏ² v²) * (ε_F + m²/ε_F),
τ_q = ℏ / (2 Γ_q).
```

The lifetime obtained here is a single-particle lifetime.  It is deliberately not identified with
the transport lifetime `τ_tr`; that later step requires the transport/collision vertex.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter
open QuantumTheory.Transport

/-- Real continuum Born coupling/measure factor, coerced to the complex self-energy coefficient. -/
def continuumBornSelfEnergyPrefactor (disorderStrength hbar : ℝ) : ℂ :=
  ((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ)

/-- Retarded finite-cutoff continuum Born self-energy projected onto a clean band at momentum
`(px,py)`. -/
def finiteCutoffContinuumBornRetardedBandSelfEnergy
    (band : Band)
    (v m px py probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  bandDiagonalPauliExpectation band v m px py
    (continuumBornSelfEnergyPrefactor disorderStrength hbar *
      finiteCutoffContinuumBornScalarIntegral .retarded
        v m probeEnergy broadening pMax)
    (continuumBornSelfEnergyPrefactor disorderStrength hbar *
      finiteCutoffContinuumBornZIntegral .retarded
        v m probeEnergy broadening pMax)

/-- The band-projected retarded Born self-energy factors through the same common denominator integral
as the two Pauli channels. -/
theorem finiteCutoffContinuumBornRetardedBandSelfEnergy_eq
    (band : Band)
    (v m px py probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hE : energy v m px py ≠ 0) :
    finiteCutoffContinuumBornRetardedBandSelfEnergy band
        v m px py probeEnergy broadening disorderStrength hbar pMax =
      continuumBornSelfEnergyPrefactor disorderStrength hbar *
        (spectralParameter .retarded probeEnergy broadening +
          (((bandSign band * m ^ 2 / energy v m px py : ℝ) : ℂ))) *
        finiteCutoffContinuumBornDenominatorIntegral .retarded
          v m probeEnergy broadening pMax := by
  unfold finiteCutoffContinuumBornRetardedBandSelfEnergy
  rw [bandDiagonalPauliExpectation_eq band v m px py _ _ hE]
  rw [finiteCutoffContinuumBornScalarIntegral_eq_spectralParameter_mul_denominatorIntegral]
  rw [finiteCutoffContinuumBornZIntegral_eq_mass_mul_denominatorIntegral]
  unfold continuumBornSelfEnergyPrefactor
  push_cast
  ring

/-- Upper-band retarded Born self-energy evaluated on the occupation-derived Fermi circle and at
probe energy `ε_F`. -/
def finiteCutoffContinuumBornUpperOnShellSelfEnergy
    (v m fermiEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  finiteCutoffContinuumBornRetardedBandSelfEnergy .upper
    v m (metallicFermiRadius v m fermiEnergy) 0 fermiEnergy broadening
      disorderStrength hbar pMax

/-- In the strict metallic regime the upper-band on-shell self-energy is

`A [z_R(ε_F,η) + m²/ε_F] J_R`,

with `A` the continuum disorder/measure prefactor and `J_R` the common finite-cutoff Born denominator
integral. -/
theorem finiteCutoffContinuumBornUpperOnShellSelfEnergy_eq
    (v m fermiEnergy broadening disorderStrength hbar pMax : ℝ)
    (hv : v ≠ 0) (hm : 0 < m) (hmF : m < fermiEnergy) :
    finiteCutoffContinuumBornUpperOnShellSelfEnergy
        v m fermiEnergy broadening disorderStrength hbar pMax =
      continuumBornSelfEnergyPrefactor disorderStrength hbar *
        (spectralParameter .retarded fermiEnergy broadening +
          (((m ^ 2 / fermiEnergy : ℝ) : ℂ))) *
        finiteCutoffContinuumBornDenominatorIntegral .retarded
          v m fermiEnergy broadening pMax := by
  have hfermiPos : 0 < fermiEnergy := lt_trans hm hmF
  have hfermiNe : fermiEnergy ≠ 0 := ne_of_gt hfermiPos
  have hE :
      energy v m (metallicFermiRadius v m fermiEnergy) 0 ≠ 0 := by
    rw [energy_metallicFermiRadius v m fermiEnergy hv hm hmF.le]
    exact hfermiNe
  unfold finiteCutoffContinuumBornUpperOnShellSelfEnergy
  rw [finiteCutoffContinuumBornRetardedBandSelfEnergy_eq
    .upper v m (metallicFermiRadius v m fermiEnergy) 0
      fermiEnergy broadening disorderStrength hbar pMax hE]
  rw [energy_metallicFermiRadius v m fermiEnergy hv hm hmF.le]
  simp [bandSign_upper]

/-- The imaginary part of the upper-band on-shell self-energy is the scalar-channel imaginary part
plus `(m/ε_F)` times the `σ_z`-channel imaginary part. -/
theorem finiteCutoffContinuumBornUpperOnShellSelfEnergy_im_eq
    (v m fermiEnergy broadening disorderStrength hbar pMax : ℝ)
    (hv : v ≠ 0) (hm : 0 < m) (hmF : m < fermiEnergy) :
    (finiteCutoffContinuumBornUpperOnShellSelfEnergy
      v m fermiEnergy broadening disorderStrength hbar pMax).im =
      ((continuumBornSelfEnergyPrefactor disorderStrength hbar *
        finiteCutoffContinuumBornScalarIntegral .retarded
          v m fermiEnergy broadening pMax).im) +
        (m / fermiEnergy) *
          ((continuumBornSelfEnergyPrefactor disorderStrength hbar *
            finiteCutoffContinuumBornZIntegral .retarded
              v m fermiEnergy broadening pMax).im) := by
  have hfermiPos : 0 < fermiEnergy := lt_trans hm hmF
  have hfermiNe : fermiEnergy ≠ 0 := ne_of_gt hfermiPos
  have hE :
      energy v m (metallicFermiRadius v m fermiEnergy) 0 ≠ 0 := by
    rw [energy_metallicFermiRadius v m fermiEnergy hv hm hmF.le]
    exact hfermiNe
  unfold finiteCutoffContinuumBornUpperOnShellSelfEnergy
    finiteCutoffContinuumBornRetardedBandSelfEnergy
  rw [bandDiagonalPauliExpectation_eq .upper
    v m (metallicFermiRadius v m fermiEnergy) 0 _ _ hE]
  rw [energy_metallicFermiRadius v m fermiEnergy hv hm hmF.le]
  simp [bandSign_upper, Complex.add_im, Complex.im_ofReal_mul]

/-- Finite-broadening upper-band on-shell single-particle decay half-width
`Γ_q(η) = -Im Σ⁺ᴿ(ε_F;η)`. -/
def finiteCutoffContinuumBornUpperOnShellDecayWidth
    (v m fermiEnergy broadening disorderStrength hbar pMax : ℝ) : ℝ :=
  retardedSelfEnergyDecayWidth
    (finiteCutoffContinuumBornUpperOnShellSelfEnergy
      v m fermiEnergy broadening disorderStrength hbar pMax)

/-- With zero continuum disorder strength, the regularized Born decay width vanishes. -/
@[simp]
theorem finiteCutoffContinuumBornUpperOnShellDecayWidth_zero_disorder
    (v m fermiEnergy broadening hbar pMax : ℝ) :
    finiteCutoffContinuumBornUpperOnShellDecayWidth
        v m fermiEnergy broadening 0 hbar pMax = 0 := by
  simp [finiteCutoffContinuumBornUpperOnShellDecayWidth,
    finiteCutoffContinuumBornUpperOnShellSelfEnergy,
    finiteCutoffContinuumBornRetardedBandSelfEnergy,
    continuumBornSelfEnergyPrefactor, retardedSelfEnergyDecayWidth,
    bandDiagonalPauliExpectation]

/-- Zero-broadening single-particle decay half-width obtained from the fixed-cutoff retarded Born
self-energy. -/
def continuumBornUpperOnShellDecayWidthLimit
    (v m fermiEnergy disorderStrength hbar : ℝ) : ℝ :=
  disorderStrength / (4 * hbar ^ 2 * v ^ 2) *
    (fermiEnergy + m ^ 2 / fermiEnergy)

/-- At fixed finite cutoff beyond the Fermi circle, the imaginary part of the upper-band on-shell
retarded Born self-energy has the sum of the scalar and `σ_z` damping limits. -/
theorem tendsto_finiteCutoffContinuumBornUpperOnShellSelfEnergy_im_broadening_zero
    (v m fermiEnergy disorderStrength hbar pMax : ℝ)
    (hv : v ≠ 0) (hm : 0 < m) (hmF : m < fermiEnergy)
    (hcutoff : fermiEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        (finiteCutoffContinuumBornUpperOnShellSelfEnergy
          v m fermiEnergy broadening disorderStrength hbar pMax).im)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        ((disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
            (fermiEnergy * (-(((2 : ℝ) * v ^ 2)⁻¹) * Real.pi)) +
          (m / fermiEnergy) *
            ((disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
              (m * (-(((2 : ℝ) * v ^ 2)⁻¹) * Real.pi))))) := by
  have hscalar :=
    tendsto_finiteCutoffContinuumBornRetardedScalarSelfEnergyCoefficient_im_broadening_zero
      v m fermiEnergy disorderStrength hbar pMax hv hm hmF hcutoff
  have hz :=
    tendsto_finiteCutoffContinuumBornRetardedZSelfEnergyCoefficient_im_broadening_zero
      v m fermiEnergy disorderStrength hbar pMax hv hm hmF hcutoff
  have hweight :
      Tendsto (fun _ : ℝ => m / fermiEnergy)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (m / fermiEnergy)) :=
    tendsto_const_nhds
  have hsum := hscalar.add (hweight.mul hz)
  refine hsum.congr' ?_
  filter_upwards with broadening
  simpa [continuumBornSelfEnergyPrefactor] using
    (finiteCutoffContinuumBornUpperOnShellSelfEnergy_im_eq
      v m fermiEnergy broadening disorderStrength hbar pMax hv hm hmF).symm

/-- The regularized upper-band Born decay width converges to the positive-sign closed damping
expression at fixed finite cutoff. -/
theorem tendsto_finiteCutoffContinuumBornUpperOnShellDecayWidth_broadening_zero
    (v m fermiEnergy disorderStrength hbar pMax : ℝ)
    (hhbar : hbar ≠ 0) (hv : v ≠ 0) (hm : 0 < m) (hmF : m < fermiEnergy)
    (hcutoff : fermiEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornUpperOnShellDecayWidth
          v m fermiEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (continuumBornUpperOnShellDecayWidthLimit
          v m fermiEnergy disorderStrength hbar)) := by
  have him :=
    tendsto_finiteCutoffContinuumBornUpperOnShellSelfEnergy_im_broadening_zero
      v m fermiEnergy disorderStrength hbar pMax hv hm hmF hcutoff
  have hlimit :
      -((disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
            (fermiEnergy * (-(((2 : ℝ) * v ^ 2)⁻¹) * Real.pi)) +
          (m / fermiEnergy) *
            ((disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
              (m * (-(((2 : ℝ) * v ^ 2)⁻¹) * Real.pi)))) =
        continuumBornUpperOnShellDecayWidthLimit
          v m fermiEnergy disorderStrength hbar := by
    unfold continuumBornUpperOnShellDecayWidthLimit
    rw [← continuumBornDampingPrefactor_eq disorderStrength hbar v hhbar hv]
    ring
  change Tendsto
    (fun broadening : ℝ =>
      -(finiteCutoffContinuumBornUpperOnShellSelfEnergy
        v m fermiEnergy broadening disorderStrength hbar pMax).im)
    (nhdsWithin 0 (Set.Ioi 0))
    (nhds (continuumBornUpperOnShellDecayWidthLimit
      v m fermiEnergy disorderStrength hbar))
  rw [← hlimit]
  exact him.neg

/-- Positive disorder strength gives a positive zero-broadening single-particle decay width in the
strict metallic regime. -/
theorem continuumBornUpperOnShellDecayWidthLimit_pos
    (v m fermiEnergy disorderStrength hbar : ℝ)
    (hdisorder : 0 < disorderStrength) (hhbar : hbar ≠ 0) (hv : v ≠ 0)
    (hm : 0 < m) (hmF : m < fermiEnergy) :
    0 < continuumBornUpperOnShellDecayWidthLimit
      v m fermiEnergy disorderStrength hbar := by
  have hfermiPos : 0 < fermiEnergy := lt_trans hm hmF
  have hhbarSq : 0 < hbar ^ 2 := sq_pos_of_ne_zero hhbar
  have hvSq : 0 < v ^ 2 := sq_pos_of_ne_zero hv
  unfold continuumBornUpperOnShellDecayWidthLimit
  have hden : 0 < 4 * hbar ^ 2 * v ^ 2 := by positivity
  have hscale : 0 < disorderStrength / (4 * hbar ^ 2 * v ^ 2) :=
    div_pos hdisorder hden
  have hsum : 0 < fermiEnergy + m ^ 2 / fermiEnergy := by positivity
  exact mul_pos hscale hsum

/-- Positive zero-broadening Born single-particle lifetime obtained from the decay-width limit.
This is `τ_q`, not the transport lifetime `τ_tr`. -/
def continuumBornUpperOnShellSingleParticleLifetime
    (v m fermiEnergy disorderStrength hbar : ℝ)
    (hhbar : 0 < hbar) (hv : v ≠ 0) (hm : 0 < m) (hmF : m < fermiEnergy)
    (hdisorder : 0 < disorderStrength) : PositiveSingleParticleLifetime :=
  positiveSingleParticleLifetimeFromDecayWidth hbar
    (continuumBornUpperOnShellDecayWidthLimit
      v m fermiEnergy disorderStrength hbar)
    hhbar
    (continuumBornUpperOnShellDecayWidthLimit_pos
      v m fermiEnergy disorderStrength hbar hdisorder (ne_of_gt hhbar) hv hm hmF)

end

end AnomalousHall.MassiveDirac
