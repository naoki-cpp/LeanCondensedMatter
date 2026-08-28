import LeanCondensedMatter.Transport.Analysis.SingleParticleLifetime
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.DenominatorFactorization
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Model.BandProjection
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Model.Occupation
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Band-projected continuum Born self-energy and single-particle decay width

This file makes the first microscopic bridge from the existing finite-cutoff continuum Born
self-energy to the longitudinal-transport lifetime program.  The retarded Born self-energy has only
identity and `σ_z` channels after angular reduction.  Those two channels are projected onto a clean
massive-Dirac band using the gauge-independent spectral projector, and the upper band is then put on
the occupation-derived Fermi circle.

At finite nonzero Green-function broadening `η`, the resulting regularized single-particle decay
half-width is

```text
Γ_q(η) = -Im Σ⁺ᴿ(ε_F; η).
```

This module does not claim that the finite-`η` quantity is already the physical disorder lifetime.
A later slice must control `η → 0+`, prove the sign/positivity in the intended cutoff regime, and only
then construct `τ_q = ℏ/(2Γ_q)`.  No identification with the transport lifetime `τ_tr` is made.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

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

/-- Finite-broadening upper-band on-shell single-particle decay half-width
`Γ_q(η) = -Im Σ⁺ᴿ(ε_F;η)`. -/
def finiteCutoffContinuumBornUpperOnShellDecayWidth
    (v m fermiEnergy broadening disorderStrength hbar pMax : ℝ) : ℝ :=
  retardedSelfEnergyDecayWidth
    (finiteCutoffContinuumBornUpperOnShellSelfEnergy
      v m fermiEnergy broadening disorderStrength hbar pMax)

/-- Exact finite-broadening decay-width expression inherited from the common Born denominator
integral. -/
theorem finiteCutoffContinuumBornUpperOnShellDecayWidth_eq
    (v m fermiEnergy broadening disorderStrength hbar pMax : ℝ)
    (hv : v ≠ 0) (hm : 0 < m) (hmF : m < fermiEnergy) :
    finiteCutoffContinuumBornUpperOnShellDecayWidth
        v m fermiEnergy broadening disorderStrength hbar pMax =
      -(
        continuumBornSelfEnergyPrefactor disorderStrength hbar *
          (spectralParameter .retarded fermiEnergy broadening +
            (((m ^ 2 / fermiEnergy : ℝ) : ℂ))) *
          finiteCutoffContinuumBornDenominatorIntegral .retarded
            v m fermiEnergy broadening pMax).im := by
  unfold finiteCutoffContinuumBornUpperOnShellDecayWidth retardedSelfEnergyDecayWidth
  rw [finiteCutoffContinuumBornUpperOnShellSelfEnergy_eq
    v m fermiEnergy broadening disorderStrength hbar pMax hv hm hmF]

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

end

end AnomalousHall.MassiveDirac
