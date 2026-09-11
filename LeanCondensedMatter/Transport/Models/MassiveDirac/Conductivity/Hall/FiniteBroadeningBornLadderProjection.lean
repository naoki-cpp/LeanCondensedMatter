import LeanCondensedMatter.Transport.Core.ConductivityTensor
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.FiniteBroadeningBornLadderLongitudinalZeroBroadening
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Hall.FiniteBroadeningBornLadderWeakDisorder
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderRadial
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Hall projection of the massive-Dirac Born-Dyson conductivity tensor

The finite-`η` massive-Dirac Středa conductivity is represented directly as a
`ConductivityTensor Direction2`. Rotational closure proves `σ_yx = -σ_xy` and `σ_yy = σ_xx` before
any broadening or disorder limit is taken. This module uses those identities together with the
existing ordered `xx` and `xy` zero-broadening limits to construct the physical zero-broadening
tensor boundary.

The Hall component is then the antisymmetric tensor projection rather than a label attached to an
ordered response. Its subsequent one-sided weak-disorder limit reproduces the standard non-crossing
massive-Dirac result of Ado et al., EPL 111, 37004 (2015), Eq. (3).

The cutoff remains fixed beyond the metallic shell, and the limits remain sequential: `η → 0⁺` at
fixed positive disorder, then `W → 0⁺`. No ultraviolet/thermodynamic/simultaneous limit, crossed
`X/Ψ` contribution, mechanism decomposition, or exact disorder-average claim is introduced here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter QuantumTheory.Transport

/-- Finite-`η` rotational closure makes the physically normalized ordered `yx` tensor component the
negative of ordered `xy`. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensor_component_yx_eq_neg_xy
    (e v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    (finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensor
        e v m probeEnergy broadening disorderStrength hbar pMax).component .y .x =
      -(finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensor
        e v m probeEnergy broadening disorderStrength hbar pMax).component .x .y := by
  change
    ((bastinTraceConductivityPrefactor hbar * momentumMeasurePrefactor hbar : ℝ) : ℂ) *
        finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral
          .y .x e v m probeEnergy broadening disorderStrength hbar pMax =
      -(((bastinTraceConductivityPrefactor hbar * momentumMeasurePrefactor hbar : ℝ) : ℂ) *
        finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral
          .x .y e v m probeEnergy broadening disorderStrength hbar pMax)
  rw [finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral_yx_eq_neg_xy]
  ring

/-- Finite-`η` rotational closure makes the two physically normalized diagonal tensor components
equal. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensor_component_yy_eq_xx
    (e v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    (finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensor
        e v m probeEnergy broadening disorderStrength hbar pMax).component .y .y =
      (finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensor
        e v m probeEnergy broadening disorderStrength hbar pMax).component .x .x := by
  change
    ((bastinTraceConductivityPrefactor hbar * momentumMeasurePrefactor hbar : ℝ) : ℂ) *
        finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral
          .y .y e v m probeEnergy broadening disorderStrength hbar pMax =
      ((bastinTraceConductivityPrefactor hbar * momentumMeasurePrefactor hbar : ℝ) : ℂ) *
        finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral
          .x .x e v m probeEnergy broadening disorderStrength hbar pMax
  rw [finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral_yy_eq_xx]

/-- Physical fixed-cutoff conductivity tensor after the componentwise `η → 0⁺` boundary has been
formed at fixed positive disorder. -/
def finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensorZeroBroadeningBoundary
    (e v m probeEnergy disorderStrength hbar pMax : ℝ) : ConductivityTensor Direction2 where
  component := fun measured source =>
    match measured, source with
    | .x, .x =>
        finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceConductivityZeroBroadeningBoundary
          e v m probeEnergy disorderStrength hbar pMax
    | .x, .y =>
        finiteCutoffContinuumBornDysonOrderedXYRetardedAdvancedDressedSurfaceConductivityZeroBroadeningBoundary
          e v m probeEnergy disorderStrength hbar pMax
    | .y, .x =>
        -finiteCutoffContinuumBornDysonOrderedXYRetardedAdvancedDressedSurfaceConductivityZeroBroadeningBoundary
          e v m probeEnergy disorderStrength hbar pMax
    | .y, .y =>
        finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceConductivityZeroBroadeningBoundary
          e v m probeEnergy disorderStrength hbar pMax

/-- Every finite-`η` conductivity tensor component converges to the corresponding entry of the
physical zero-broadening conductivity tensor. The off-diagonal `yx` and diagonal `yy` cases are
obtained from the finite-`η` rotational identities rather than assigned independently. -/
theorem tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensor_component_broadening_zero
    (measured source : Direction2)
    (e v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hpMax : 0 ≤ pMax) (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hdisorder : 0 < disorderStrength) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2)
    (hrenorm : finiteCutoffContinuumBornBoundaryRealRenormalization
      v m probeEnergy disorderStrength hbar pMax < 1)
    (hdet : finiteCutoffContinuumBornDysonLadderDeterminantZeroBroadeningBoundary
      v m probeEnergy disorderStrength hbar pMax ≠ 0) :
    Tendsto
      (fun broadening : ℝ =>
        (finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensor
          e v m probeEnergy broadening disorderStrength hbar pMax).component measured source)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        ((finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensorZeroBroadeningBoundary
          e v m probeEnergy disorderStrength hbar pMax).component measured source)) := by
  have hxx :=
    tendsto_finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceConductivity_broadening_zero
      e v m probeEnergy disorderStrength hbar pMax hpMax hvelocity hhbar
      hdisorder hmetal hcutoff hrenorm hdet
  have hxy :=
    tendsto_finiteCutoffContinuumBornDysonOrderedXYRetardedAdvancedDressedSurfaceConductivity_broadening_zero
      e v m probeEnergy disorderStrength hbar pMax hpMax hvelocity hhbar
      hdisorder hmetal hcutoff hrenorm hdet
  cases measured <;> cases source
  · simpa [finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensorZeroBroadeningBoundary] using hxx
  · simpa [finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensorZeroBroadeningBoundary] using hxy
  · apply Tendsto.congr' ?_ hxy.neg
    filter_upwards with broadening
    exact (finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensor_component_yx_eq_neg_xy
      e v m probeEnergy broadening disorderStrength hbar pMax).symm
  · apply Tendsto.congr' ?_ hxx
    filter_upwards with broadening
    exact (finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensor_component_yy_eq_xx
      e v m probeEnergy broadening disorderStrength hbar pMax).symm

/-- The antisymmetric Hall projection of the zero-broadening tensor equals its ordered `xy`
component exactly. -/
@[simp]
theorem finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensorZeroBroadeningBoundary_hallComponent_xy
    (e v m probeEnergy disorderStrength hbar pMax : ℝ) :
    (finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensorZeroBroadeningBoundary
        e v m probeEnergy disorderStrength hbar pMax).hallComponent .x .y =
      finiteCutoffContinuumBornDysonOrderedXYRetardedAdvancedDressedSurfaceConductivityZeroBroadeningBoundary
        e v m probeEnergy disorderStrength hbar pMax := by
  simp [ConductivityTensor.hallComponent,
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensorZeroBroadeningBoundary]

/-- The fixed-cutoff Hall projection has the same one-sided weak-disorder limit as the ordered `xy`
endpoint, now interpreted as the antisymmetric part of a completed conductivity tensor. -/
theorem tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensorZeroBroadeningBoundary_hallComponent_disorder_zero
    (e v m probeEnergy hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hhbar : 0 < hbar)
    (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun disorderStrength : ℝ =>
        (finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensorZeroBroadeningBoundary
          e v m probeEnergy disorderStrength hbar pMax).hallComponent .x .y)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (((-2 * e ^ 2 * probeEnergy * m * (probeEnergy ^ 2 + m ^ 2) /
          (Real.pi * hbar * (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2) : ℝ) : ℂ))) := by
  simpa only [
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensorZeroBroadeningBoundary_hallComponent_xy] using
    tendsto_finiteCutoffContinuumBornDysonOrderedXYRetardedAdvancedDressedSurfaceConductivityZeroBroadeningBoundary_disorder_zero
      e v m probeEnergy hbar pMax hvelocity hhbar hmetal hcutoff

/-- Standard non-crossing massive-Dirac Hall conductivity of Ado et al., EPL 111, 37004 (2015),
Eq. (3), written with `h = 2πℏ`. -/
def nonCrossingHallConductivity (e hbar m probeEnergy : ℝ) : ℝ :=
  -(4 * e ^ 2 / planckFromReduced hbar) *
    (probeEnergy * m * (probeEnergy ^ 2 + m ^ 2) /
      (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2)

/-- The sequential zero-broadening then weak-disorder Hall projection reproduces the Ado
non-crossing conductivity formula. -/
theorem tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensorZeroBroadeningBoundary_hallComponent_disorder_zero_eq_nonCrossing
    (e v m probeEnergy hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hhbar : 0 < hbar)
    (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun disorderStrength : ℝ =>
        (finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensorZeroBroadeningBoundary
          e v m probeEnergy disorderStrength hbar pMax).hallComponent .x .y)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (((nonCrossingHallConductivity e hbar m probeEnergy : ℝ) : ℂ))) := by
  have h :=
    tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensorZeroBroadeningBoundary_hallComponent_disorder_zero
      e v m probeEnergy hbar pMax hvelocity hhbar hmetal hcutoff
  have hprobe : 0 < probeEnergy := lt_of_le_of_lt (abs_nonneg m) hmetal
  have hden : probeEnergy ^ 2 + 3 * m ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero (ne_of_gt hprobe), sq_nonneg m]
  have htarget :
      (((-2 * e ^ 2 * probeEnergy * m * (probeEnergy ^ 2 + m ^ 2) /
        (Real.pi * hbar * (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2) : ℝ) : ℂ)) =
      (((nonCrossingHallConductivity e hbar m probeEnergy : ℝ) : ℂ)) := by
    norm_cast
    unfold nonCrossingHallConductivity planckFromReduced
    field_simp [ne_of_gt hhbar, hden, Real.pi_ne_zero]
    norm_num
    ring
  rw [htarget] at h
  exact h

end

end QuantumTheory.Transport.Models.MassiveDirac
