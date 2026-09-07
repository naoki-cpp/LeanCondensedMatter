import LeanCondensedMatter.Analysis.Lorentzian.RadialQuadratic
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.BornCurrentVertexFiniteCutoff
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Normalized finite-cutoff Born current rung

This module evaluates the longitudinal specialization of the direction-indexed normalized
finite-cutoff Born `Gᴿ σₓ Gᴬ` current rung by the shared quadratic-Lorentzian arctangent calculus.
The canonical weak-disorder target coefficient is recorded here because it is consumed independently
by the fixed-cutoff and infinite-cutoff limit routes.

No weak-disorder or ultraviolet limit, ladder resummation, transport-lifetime identification, or
Kubo conductivity theorem is taken in this module.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport
open scoped Interval

/-- The external disorder-line / physical-measure prefactor is one power of the Born damping scale:
`W /(2πℏ)² = γ v² / π²`. -/
theorem continuumBornRetardedAdvancedCurrentRungPrefactor_eq_dampingScale
    (v disorderStrength hbar : ℝ) (hv : v ≠ 0) (hhbar : hbar ≠ 0) :
    continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar =
      continuumBornDampingScale v disorderStrength hbar * v ^ 2 / Real.pi ^ 2 := by
  unfold continuumBornRetardedAdvancedCurrentRungPrefactor
  unfold continuumBornDampingScale momentumMeasurePrefactor
  field_simp [hv, hhbar, Real.pi_ne_zero]
  ring

/-- Arctangent phase adapted to the real retarded-advanced denominator pair `A(p)² + B²`. -/
def continuumBornRetardedAdvancedCurrentRungArctanPhase
    (v m p probeEnergy disorderStrength hbar : ℝ) : ℝ :=
  Real.arctan
    (continuumBornRADenominatorCenter v m p probeEnergy disorderStrength hbar /
      continuumBornRADenominatorWidth v m probeEnergy disorderStrength hbar)

/-- Exact finite-cutoff arctangent evaluation of the longitudinal `.x` specialization of the
normalized Born RA current rung. The assumptions only keep the resonance width and radial velocity
scale nonzero; no weak-disorder limit is taken in this theorem. -/
theorem finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungCoefficient_x_eq_arctan
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hv : v ≠ 0)
    (hwidth : continuumBornRADenominatorWidth
      v m probeEnergy disorderStrength hbar ≠ 0) :
    finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungCoefficient .x
        v m probeEnergy disorderStrength hbar pMax =
      (continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar *
          Real.pi *
          (1 + continuumBornDampingScale v disorderStrength hbar ^ 2) *
          (probeEnergy ^ 2 - m ^ 2) /
          (v ^ 2 * continuumBornRADenominatorWidth
            v m probeEnergy disorderStrength hbar)) *
        (continuumBornRetardedAdvancedCurrentRungArctanPhase
            v m 0 probeEnergy disorderStrength hbar -
          continuumBornRetardedAdvancedCurrentRungArctanPhase
            v m pMax probeEnergy disorderStrength hbar) := by
  let A : ℝ :=
    (1 - continuumBornDampingScale v disorderStrength hbar ^ 2) *
      (probeEnergy ^ 2 - m ^ 2)
  let B : ℝ :=
    continuumBornRADenominatorWidth v m probeEnergy disorderStrength hbar
  have hradial := integral_radialQuadraticLorentzian_eq_arctan
    v A B pMax hv hwidth
  unfold finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungCoefficient
    continuumBornRetardedAdvancedPauliXCurrentRungRadialIntegrandReal
    continuumBornRetardedAdvancedPauliXAngularNumerator
  rw [show
      (fun p : ℝ =>
        continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar * p *
          (2 * Real.pi *
            (1 + continuumBornDampingScale v disorderStrength hbar ^ 2) *
            (probeEnergy ^ 2 - m ^ 2)) *
          (continuumBornRADenominatorProduct
            v m p probeEnergy disorderStrength hbar)⁻¹) =
      (fun p : ℝ =>
        (continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar *
          2 * Real.pi *
          (1 + continuumBornDampingScale v disorderStrength hbar ^ 2) *
          (probeEnergy ^ 2 - m ^ 2)) *
          (p / continuumBornRADenominatorProduct
            v m p probeEnergy disorderStrength hbar)) by
    funext p
    rw [div_eq_mul_inv]
    ring]
  rw [intervalIntegral.integral_const_mul]
  rw [show
      (∫ p in (0 : ℝ)..pMax,
        p / continuumBornRADenominatorProduct
          v m p probeEnergy disorderStrength hbar) =
        (2 * v ^ 2 * B)⁻¹ *
          (Real.arctan ((v ^ 2 * pMax ^ 2 - A) / B) +
            Real.arctan (A / B)) by
    simpa [A, B, continuumBornRADenominatorProduct,
      continuumBornRADenominatorCenter, mul_comm] using hradial]
  unfold continuumBornRetardedAdvancedCurrentRungArctanPhase
  dsimp [A, B]
  rw [show
      (v ^ 2 * pMax ^ 2 -
          (1 - continuumBornDampingScale v disorderStrength hbar ^ 2) *
            (probeEnergy ^ 2 - m ^ 2)) /
          continuumBornRADenominatorWidth v m probeEnergy disorderStrength hbar =
        -(((probeEnergy ^ 2 - m ^ 2) *
              (1 - continuumBornDampingScale v disorderStrength hbar ^ 2) -
            v ^ 2 * pMax ^ 2) /
          continuumBornRADenominatorWidth v m probeEnergy disorderStrength hbar) by
    ring]
  rw [Real.arctan_neg]
  unfold continuumBornRADenominatorCenter
  field_simp [hv, hwidth]
  ring_nf

/-- Exact longitudinal endpoint formula with the disorder normalization already cancelled against
the resonance width. This is the form adapted to the `disorderStrength → 0⁺` limit. -/
theorem finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungCoefficient_x_eq_arctan_normalized
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hv : v ≠ 0) (hhbar : hbar ≠ 0) (hdisorder : disorderStrength ≠ 0)
    (hsum : probeEnergy ^ 2 + m ^ 2 ≠ 0) :
    finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungCoefficient .x
        v m probeEnergy disorderStrength hbar pMax =
      ((1 + continuumBornDampingScale v disorderStrength hbar ^ 2) *
          (probeEnergy ^ 2 - m ^ 2) /
          (2 * Real.pi * (probeEnergy ^ 2 + m ^ 2))) *
        (continuumBornRetardedAdvancedCurrentRungArctanPhase
            v m 0 probeEnergy disorderStrength hbar -
          continuumBornRetardedAdvancedCurrentRungArctanPhase
            v m pMax probeEnergy disorderStrength hbar) := by
  have hgamma : continuumBornDampingScale v disorderStrength hbar ≠ 0 := by
    unfold continuumBornDampingScale
    exact div_ne_zero hdisorder
      (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hhbar)) (pow_ne_zero 2 hv))
  have hwidth : continuumBornRADenominatorWidth
      v m probeEnergy disorderStrength hbar ≠ 0 := by
    unfold continuumBornRADenominatorWidth
    exact mul_ne_zero (mul_ne_zero (by norm_num) hgamma) hsum
  rw [finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungCoefficient_x_eq_arctan
    v m probeEnergy disorderStrength hbar pMax hv hwidth]
  rw [continuumBornRetardedAdvancedCurrentRungPrefactor_eq_dampingScale
    v disorderStrength hbar hv hhbar]
  unfold continuumBornRADenominatorWidth
  field_simp [hv, hhbar, hgamma, hsum, Real.pi_ne_zero]

/-- The weak-disorder metallic target coefficient before solving the ladder equation. -/
def continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
    (m probeEnergy : ℝ) : ℝ :=
  (probeEnergy ^ 2 - m ^ 2) / (2 * (probeEnergy ^ 2 + m ^ 2))

end

end QuantumTheory.Transport.Models.MassiveDirac
