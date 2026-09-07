import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertexZeroBroadeningDomination
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Fixed-cutoff regularity for the zero-broadening Born current rung

This module closes the model-specific regularity hypothesis left by the compact dominated-convergence
bridge. At fixed finite cutoff and fixed positive disorder strength, the retarded/advanced
zero-broadening Dyson denominator stays nonzero when the real Born renormalization remains below the
unit threshold. The resulting theorem feeds directly into the already-proved compact domination
result for the normalized current-rung integral.

No disorder-strength limit, ultraviolet removal, solved-ladder limit, conductivity theorem,
SCBA/Ward claim, crossed diagram, or simultaneous limit is introduced here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter
open QuantumTheory.Transport

/-- Dimensionless real finite-cutoff Born renormalization entering the zero-broadening effective
energy and mass. The real part is intentional here: this quantity tracks the real self-energy shift,
not a conversion from a complex observable to a real one. -/
def finiteCutoffContinuumBornBoundaryRealRenormalization
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℝ :=
  (disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
    (finiteCutoffContinuumBornDenominatorIntegralBoundaryValue
      .retarded v m probeEnergy pMax).re

private theorem finiteCutoffContinuumBornBoundaryRealRenormalization_eq_side
    (side : SpectralSide)
    (v m probeEnergy disorderStrength hbar pMax : ℝ) :
    (disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
        (finiteCutoffContinuumBornDenominatorIntegralBoundaryValue
          side v m probeEnergy pMax).re =
      finiteCutoffContinuumBornBoundaryRealRenormalization
        v m probeEnergy disorderStrength hbar pMax := by
  cases side <;>
    simp [finiteCutoffContinuumBornBoundaryRealRenormalization,
      finiteCutoffContinuumBornDenominatorIntegralBoundaryValue,
      pauliGreenDenominator, SpectralSide.regulator]

private theorem finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary_im_eq
    (side : SpectralSide)
    (v m p probeEnergy disorderStrength hbar pMax : ℝ) :
    (finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
      side v m p probeEnergy disorderStrength hbar pMax).im =
      -2 * (disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
        (finiteCutoffContinuumBornDenominatorIntegralBoundaryValue
          side v m probeEnergy pMax).im *
        (probeEnergy ^ 2 + m ^ 2 -
          (disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
            (finiteCutoffContinuumBornDenominatorIntegralBoundaryValue
              side v m probeEnergy pMax).re *
            (probeEnergy ^ 2 - m ^ 2)) := by
  unfold finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
    finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary
    finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary
  simp only [pow_two, Complex.sub_im, Complex.sub_re, Complex.add_im, Complex.add_re,
    Complex.mul_im, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, zero_mul,
    add_zero, zero_add]
  ring

private theorem continuumBornAngularMeasurePrefactor_pos
    (hbar : ℝ) (hhbar : hbar ≠ 0) :
    0 < continuumBornAngularMeasurePrefactor hbar := by
  unfold continuumBornAngularMeasurePrefactor momentumMeasurePrefactor
  have hden : 0 < (2 * Real.pi * hbar) ^ 2 :=
    sq_pos_of_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hhbar)
  exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (one_div_pos.mpr hden)

private theorem finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary_ne_zero
    (side : SpectralSide)
    (v m p probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hdisorder : 0 < disorderStrength) (hmetal : |m| < probeEnergy)
    (hrenorm :
      finiteCutoffContinuumBornBoundaryRealRenormalization
        v m probeEnergy disorderStrength hbar pMax < 1) :
    finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
      side v m p probeEnergy disorderStrength hbar pMax ≠ 0 := by
  have hprobe : 0 < probeEnergy := lt_of_le_of_lt (abs_nonneg m) hmetal
  have hmetalSq : m ^ 2 < probeEnergy ^ 2 := by
    rw [← sq_abs m]
    nlinarith [abs_nonneg m]
  have hgap : 0 < probeEnergy ^ 2 - m ^ 2 := sub_pos.mpr hmetalSq
  have hmeasure : 0 < continuumBornAngularMeasurePrefactor hbar :=
    continuumBornAngularMeasurePrefactor_pos hbar hhbar
  have hg :
      0 < disorderStrength * continuumBornAngularMeasurePrefactor hbar :=
    mul_pos hdisorder hmeasure
  let J : ℂ :=
    finiteCutoffContinuumBornDenominatorIntegralBoundaryValue
      side v m probeEnergy pMax
  let lambda : ℝ :=
    (disorderStrength * continuumBornAngularMeasurePrefactor hbar) * J.re
  have hlambda : lambda < 1 := by
    dsimp [lambda, J]
    rw [finiteCutoffContinuumBornBoundaryRealRenormalization_eq_side]
    exact hrenorm
  have hlambdaGap :
      lambda * (probeEnergy ^ 2 - m ^ 2) < probeEnergy ^ 2 - m ^ 2 := by
    simpa using mul_lt_mul_of_pos_right hlambda hgap
  have hbracket :
      0 < probeEnergy ^ 2 + m ^ 2 - lambda * (probeEnergy ^ 2 - m ^ 2) := by
    nlinarith [hlambdaGap, sq_nonneg m]
  have hJim : J.im ≠ 0 := by
    dsimp [J]
    rw [finiteCutoffContinuumBornDenominatorIntegralBoundaryValue_im]
    have hvSq : v ^ 2 ≠ 0 := pow_ne_zero 2 hvelocity
    have htwoVSq : (2 * v ^ 2) ≠ 0 := mul_ne_zero (by norm_num) hvSq
    have hinv : ((2 * v ^ 2)⁻¹ : ℝ) ≠ 0 := inv_ne_zero htwoVSq
    have hsign : side.sign ≠ 0 := by
      cases side <;> simp [SpectralSide.sign]
    exact mul_ne_zero (neg_ne_zero.mpr hinv) (mul_ne_zero hsign Real.pi_ne_zero)
  have himNe :
      (finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
        side v m p probeEnergy disorderStrength hbar pMax).im ≠ 0 := by
    rw [finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary_im_eq]
    change
      -2 * (disorderStrength * continuumBornAngularMeasurePrefactor hbar) * J.im *
        (probeEnergy ^ 2 + m ^ 2 - lambda * (probeEnergy ^ 2 - m ^ 2)) ≠ 0
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt hg)) hJim)
      (ne_of_gt hbracket)
  intro hzero
  apply himNe
  simpa using congrArg Complex.im hzero

private theorem finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary_ne_zero
    (v m p probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hdisorder : 0 < disorderStrength) (hmetal : |m| < probeEnergy)
    (hrenorm :
      finiteCutoffContinuumBornBoundaryRealRenormalization
        v m probeEnergy disorderStrength hbar pMax < 1) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary
      v m p probeEnergy disorderStrength hbar pMax ≠ 0 := by
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary
  exact mul_ne_zero
    (finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary_ne_zero
      .retarded v m p probeEnergy disorderStrength hbar pMax
      hvelocity hhbar hdisorder hmetal hrenorm)
    (finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary_ne_zero
      .advanced v m p probeEnergy disorderStrength hbar pMax
      hvelocity hhbar hdisorder hmetal hrenorm)

/-- At fixed finite cutoff and fixed positive disorder strength, the normalized Born-Dyson current
rung has its `η → 0⁺` integral boundary when the real Born renormalization remains below one. This
condition keeps the boundary retarded/advanced denominator off zero through its side-indexed damping
component, thereby discharging the compact nonvanishing hypothesis required by dominated
convergence. -/
theorem tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient_broadening_zero_of_boundary_realRenormalization_lt_one
    (i j : Direction2)
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hpMax : 0 ≤ pMax) (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hdisorder : 0 < disorderStrength) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2)
    (hrenorm :
      finiteCutoffContinuumBornBoundaryRealRenormalization
        v m probeEnergy disorderStrength hbar pMax < 1) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient
          i j v m probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficientZeroBroadeningBoundary
          i j v m probeEnergy disorderStrength hbar pMax)) := by
  apply
    tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient_broadening_zero_of_boundary_denominator_nonzero
      i j v m probeEnergy disorderStrength hbar pMax hpMax hdisorder.le
      hvelocity hmetal hcutoff
  intro p _
  exact
    finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary_ne_zero
      v m p probeEnergy disorderStrength hbar pMax
      hvelocity hhbar hdisorder hmetal hrenorm

end

end QuantumTheory.Transport.Models.MassiveDirac
