import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.SelfEnergyBroadeningLimit
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Occupation
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Upper-band projection of the continuum Born damping

This Phase 4 slice projects the existing finite-cutoff retarded continuum Born self-energy onto the
gauge-independent metallic upper-band Fermi-surface projector.  The projection is defined from the
actual bounded operator through the ordinary finite-dimensional trace,

```text
Tr[P₊(p_F) Σᴿ(ε_F)],
```

rather than by introducing a second self-energy or a parallel scalar-channel definition.  The
canonical Fermi-circle representative is `(p_F, 0)`, with `p_F = metallicFermiRadius v m ε_F`.

The zero-broadening imaginary part gives a positive damping magnitude `Γ_Born` through

```text
Im Tr[P₊ Σᴿ] → -Γ_Born,
Γ_Born = disorderStrength / (4 ℏ² v²) * (ε_F + m² / ε_F).
```

No single-particle lifetime, transport lifetime, NCA vertex, renormalization prescription, or
simultaneous ultraviolet / zero-broadening limit is introduced here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter
open QuantumTheory.Transport

/-- Retarded continuum Born self-energy projected onto the upper-band Fermi-surface state through
its gauge-independent rank-one projector. -/
noncomputable def finiteCutoffContinuumBornRetardedUpperBandFermiProjection
    (v m fermiEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  finiteDimensionalOperatorTrace
    (bandProjectorOperator .upper v m (metallicFermiRadius v m fermiEnergy) 0 *
      finiteCutoffContinuumBornSelfEnergy .retarded
        v m fermiEnergy broadening disorderStrength hbar pMax)

private theorem finiteDimensionalOperatorTrace_upperBandProjector_eq_one
    (v m px py : ℝ) :
    finiteDimensionalOperatorTrace
        (bandProjectorOperator .upper v m px py) = (1 : ℂ) := by
  rw [bandProjectorOperator, matrixOperator, finiteDimensionalOperatorTrace_toEuclideanCLM]
  simp [bandProjector, Matrix.trace, hamiltonian, sigmaX, sigmaY, sigmaZ]
  ring

private theorem finiteDimensionalOperatorTrace_upperBandProjector_mul_sigmaZ
    (v m px py : ℝ) :
    finiteDimensionalOperatorTrace
        (bandProjectorOperator .upper v m px py * matrixOperator sigmaZ) =
      ((m / energy v m px py : ℝ) : ℂ) := by
  let φ : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert) := Matrix.toEuclideanCLM
  change finiteDimensionalOperatorTrace
      (φ (bandProjector .upper v m px py) * φ sigmaZ) = _
  rw [← map_mul]
  change finiteDimensionalOperatorTrace
      (matrixOperator (bandProjector .upper v m px py * sigmaZ)) = _
  rw [matrixOperator, finiteDimensionalOperatorTrace_toEuclideanCLM]
  simp [bandProjector, Matrix.trace, Matrix.mul_apply, hamiltonian, sigmaX, sigmaY, sigmaZ]
  ring

/-- At nonzero broadening, the actual upper-band projector trace of the retarded Born self-energy
reduces to the scalar Pauli coefficient plus `m / ε_F` times the `σ_z` coefficient. -/
theorem finiteCutoffContinuumBornRetardedUpperBandFermiProjection_eq
    (v m fermiEnergy broadening disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hm : 0 < m) (hmF : m < fermiEnergy)
    (hbroadening : broadening ≠ 0) :
    finiteCutoffContinuumBornRetardedUpperBandFermiProjection
        v m fermiEnergy broadening disorderStrength hbar pMax =
      (((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ) *
          finiteCutoffContinuumBornScalarIntegral
            .retarded v m fermiEnergy broadening pMax) +
        (((m / fermiEnergy : ℝ) : ℂ) *
          (((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ) *
            finiteCutoffContinuumBornZIntegral
              .retarded v m fermiEnergy broadening pMax)) := by
  have hmAbsF : |m| ≤ fermiEnergy := by
    simpa [abs_of_pos hm] using hmF.le
  have henergy := energy_metallicFermiRadius v m fermiEnergy hvelocity hmAbsF
  unfold finiteCutoffContinuumBornRetardedUpperBandFermiProjection
  rw [finiteCutoffContinuumBornSelfEnergy_eq .retarded
    v m fermiEnergy broadening disorderStrength hbar pMax hbroadening]
  rw [mul_add, mul_smul_comm, mul_smul_comm]
  simp only [mul_one]
  rw [map_add, map_smul, map_smul]
  rw [finiteDimensionalOperatorTrace_upperBandProjector_eq_one]
  rw [finiteDimensionalOperatorTrace_upperBandProjector_mul_sigmaZ]
  rw [henergy]
  ring

private theorem finiteCutoffContinuumBornRetardedUpperBandFermiProjection_im_eq
    (v m fermiEnergy broadening disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hm : 0 < m) (hmF : m < fermiEnergy)
    (hbroadening : broadening ≠ 0) :
    (finiteCutoffContinuumBornRetardedUpperBandFermiProjection
        v m fermiEnergy broadening disorderStrength hbar pMax).im =
      (disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
          (finiteCutoffContinuumBornScalarIntegral
            .retarded v m fermiEnergy broadening pMax).im +
        (m / fermiEnergy) *
          ((disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
            (finiteCutoffContinuumBornZIntegral
              .retarded v m fermiEnergy broadening pMax).im) := by
  rw [finiteCutoffContinuumBornRetardedUpperBandFermiProjection_eq
    v m fermiEnergy broadening disorderStrength hbar pMax
    hvelocity hm hmF hbroadening]
  simp

/-- Physical-momentum-measure Born damping energy of the metallic upper band.  Its interpretation
below uses nonzero `ℏ`, nonzero velocity, positive disorder strength, and the strict metallic regime. -/
def continuumBornUpperBandDampingEnergy
    (v m fermiEnergy disorderStrength hbar : ℝ) : ℝ :=
  disorderStrength / (4 * hbar ^ 2 * v ^ 2) *
    (fermiEnergy + m ^ 2 / fermiEnergy)

/-- The upper-band Born damping energy is strictly positive for positive disorder strength in the
strict metallic regime. -/
theorem continuumBornUpperBandDampingEnergy_pos
    (v m fermiEnergy disorderStrength hbar : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0) (hdisorder : 0 < disorderStrength)
    (hm : 0 < m) (hmF : m < fermiEnergy) :
    0 < continuumBornUpperBandDampingEnergy
      v m fermiEnergy disorderStrength hbar := by
  have hfermi : 0 < fermiEnergy := lt_trans hm hmF
  have hhbarSq : 0 < hbar ^ 2 := sq_pos_of_ne_zero hhbar
  have hvelocitySq : 0 < v ^ 2 := sq_pos_of_ne_zero hvelocity
  have hden : 0 < 4 * hbar ^ 2 * v ^ 2 := by positivity
  have hmassTerm : 0 < fermiEnergy + m ^ 2 / fermiEnergy := by
    have hratio : 0 ≤ m ^ 2 / fermiEnergy :=
      div_nonneg (sq_nonneg m) hfermi.le
    linarith
  unfold continuumBornUpperBandDampingEnergy
  exact mul_pos (div_pos hdisorder hden) hmassTerm

/-- At fixed finite cutoff beyond the upper-band Fermi circle, the projected retarded Born
self-energy has the metallic zero-broadening imaginary limit before simplifying the continuum
measure prefactor. -/
theorem tendsto_finiteCutoffContinuumBornRetardedUpperBandFermiProjection_im_broadening_zero
    (v m fermiEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hm : 0 < m) (hmF : m < fermiEnergy)
    (hcutoff : fermiEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        (finiteCutoffContinuumBornRetardedUpperBandFermiProjection
          v m fermiEnergy broadening disorderStrength hbar pMax).im)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (-((disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
          (((2 : ℝ) * v ^ 2)⁻¹ * Real.pi) *
            (fermiEnergy + m ^ 2 / fermiEnergy)))) := by
  have hfermiNe : fermiEnergy ≠ 0 := ne_of_gt (lt_trans hm hmF)
  have hscalar :=
    tendsto_finiteCutoffContinuumBornRetardedScalarSelfEnergyCoefficient_im_broadening_zero
      v m fermiEnergy disorderStrength hbar pMax hvelocity hm hmF hcutoff
  have hz :=
    tendsto_finiteCutoffContinuumBornRetardedZSelfEnergyCoefficient_im_broadening_zero
      v m fermiEnergy disorderStrength hbar pMax hvelocity hm hmF hcutoff
  have hsum := hscalar.add
    ((tendsto_const_nhds : Tendsto (fun _ : ℝ => m / fermiEnergy)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (m / fermiEnergy))).mul hz)
  have hprojected :
      Tendsto
        (fun broadening : ℝ =>
          (finiteCutoffContinuumBornRetardedUpperBandFermiProjection
            v m fermiEnergy broadening disorderStrength hbar pMax).im)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          ((disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
              (fermiEnergy * (-(((2 : ℝ) * v ^ 2)⁻¹) * Real.pi)) +
            (m / fermiEnergy) *
              ((disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
                (m * (-(((2 : ℝ) * v ^ 2)⁻¹) * Real.pi))))) := by
    refine hsum.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with broadening hbroadening
    simpa [Complex.im_ofReal_mul] using
      (finiteCutoffContinuumBornRetardedUpperBandFermiProjection_im_eq
        v m fermiEnergy broadening disorderStrength hbar pMax
        hvelocity hm hmF (ne_of_gt hbroadening)).symm
  have htarget :
      (disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
            (fermiEnergy * (-(((2 : ℝ) * v ^ 2)⁻¹) * Real.pi)) +
          (m / fermiEnergy) *
            ((disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
              (m * (-(((2 : ℝ) * v ^ 2)⁻¹) * Real.pi))) =
        -((disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
          (((2 : ℝ) * v ^ 2)⁻¹ * Real.pi) *
            (fermiEnergy + m ^ 2 / fermiEnergy)) := by
    field_simp [hfermiNe]
    ring
  rw [htarget] at hprojected
  exact hprojected

/-- With the physical momentum measure simplified, the projected retarded self-energy approaches
minus the positive Born damping energy. -/
theorem tendsto_finiteCutoffContinuumBornRetardedUpperBandFermiProjection_im_dampingEnergy
    (v m fermiEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hm : 0 < m) (hmF : m < fermiEnergy)
    (hcutoff : fermiEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        (finiteCutoffContinuumBornRetardedUpperBandFermiProjection
          v m fermiEnergy broadening disorderStrength hbar pMax).im)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (-continuumBornUpperBandDampingEnergy
        v m fermiEnergy disorderStrength hbar)) := by
  have hlimit :=
    tendsto_finiteCutoffContinuumBornRetardedUpperBandFermiProjection_im_broadening_zero
      v m fermiEnergy disorderStrength hbar pMax hvelocity hm hmF hcutoff
  have hprefactor :=
    continuumBornDampingPrefactor_eq disorderStrength hbar v hhbar hvelocity
  have htarget :
      -((disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
          (((2 : ℝ) * v ^ 2)⁻¹ * Real.pi) *
            (fermiEnergy + m ^ 2 / fermiEnergy)) =
        -continuumBornUpperBandDampingEnergy
          v m fermiEnergy disorderStrength hbar := by
    unfold continuumBornUpperBandDampingEnergy
    rw [hprefactor]
  rw [htarget] at hlimit
  exact hlimit

end

end AnomalousHall.MassiveDirac
