import LeanCondensedMatter.Analysis.Lorentzian.RadialQuadratic
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.BornCurrentVertexWeakDisorder
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertexZeroBroadeningIntegral
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Weak-disorder limit of the zero-broadening Born-Dyson current rung

This module takes `W → 0⁺` only after the fixed-cutoff, zero-external-broadening Born-Dyson current
rung boundary has been formed. The finite real Born self-energy shift remains explicit at finite
`W`; the common radial resonance is reduced to the shared quadratic-Lorentzian calculus before the
limit is taken.

The public result is the source-`.x` in-plane rung vector limit. Solved-ladder propagation belongs to
the downstream ladder module. No conductivity, ultraviolet, thermodynamic, or simultaneous limit is
taken here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter MeasureTheory QuantumTheory.Transport
open scoped Interval

private def zeroBroadeningWeakDisorderLambda
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℝ :=
  finiteCutoffContinuumBornBoundaryRealRenormalization
    v m probeEnergy disorderStrength hbar pMax

private def zeroBroadeningWeakDisorderCenter
    (v m p probeEnergy disorderStrength hbar pMax : ℝ) : ℝ :=
  let lambda := zeroBroadeningWeakDisorderLambda
    v m probeEnergy disorderStrength hbar pMax
  let gamma := continuumBornDampingScale v disorderStrength hbar
  (1 + lambda ^ 2 - gamma ^ 2) * (probeEnergy ^ 2 - m ^ 2) -
    2 * lambda * (probeEnergy ^ 2 + m ^ 2) - v ^ 2 * p ^ 2

private def zeroBroadeningWeakDisorderBracket
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℝ :=
  probeEnergy ^ 2 + m ^ 2 -
    zeroBroadeningWeakDisorderLambda
      v m probeEnergy disorderStrength hbar pMax * (probeEnergy ^ 2 - m ^ 2)

private def zeroBroadeningWeakDisorderWidth
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℝ :=
  2 * continuumBornDampingScale v disorderStrength hbar *
    zeroBroadeningWeakDisorderBracket
      v m probeEnergy disorderStrength hbar pMax

private def zeroBroadeningWeakDisorderNumerator
    (output : Direction2)
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℝ :=
  let lambda := zeroBroadeningWeakDisorderLambda
    v m probeEnergy disorderStrength hbar pMax
  let gamma := continuumBornDampingScale v disorderStrength hbar
  match output with
  | .x =>
      (1 + lambda ^ 2 + gamma ^ 2) * (probeEnergy ^ 2 - m ^ 2) -
        2 * lambda * (probeEnergy ^ 2 + m ^ 2)
  | .y => 4 * gamma * probeEnergy * m

private def zeroBroadeningWeakDisorderPrefactorTarget
    (output : Direction2) (m probeEnergy : ℝ) : ℝ :=
  match output with
  | .x =>
      (probeEnergy ^ 2 - m ^ 2) /
        (2 * Real.pi * (probeEnergy ^ 2 + m ^ 2))
  | .y => 0

private theorem zeroBroadeningWeakDisorderLambda_eq_side
    (side : SpectralSide)
    (v m probeEnergy disorderStrength hbar pMax : ℝ) :
    (disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
        (finiteCutoffContinuumBornDenominatorIntegralBoundaryValue
          side v m probeEnergy pMax).re =
      zeroBroadeningWeakDisorderLambda
        v m probeEnergy disorderStrength hbar pMax := by
  cases side <;>
    simp [zeroBroadeningWeakDisorderLambda,
      finiteCutoffContinuumBornBoundaryRealRenormalization,
      finiteCutoffContinuumBornDenominatorIntegralBoundaryValue,
      pauliGreenDenominator, SpectralSide.regulator]

private theorem zeroBroadeningWeakDisorder_effectiveEnergy_eq
    (side : SpectralSide)
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0) :
    finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary
        side v m probeEnergy disorderStrength hbar pMax =
      ((probeEnergy *
          (1 - zeroBroadeningWeakDisorderLambda
            v m probeEnergy disorderStrength hbar pMax) : ℝ) : ℂ) +
        ((side.sign * probeEnergy *
          continuumBornDampingScale v disorderStrength hbar : ℝ) : ℂ) * Complex.I := by
  have hgamma := continuumBornDampingScale_eq_selfEnergyPrefactor
    v disorderStrength hbar hvelocity hhbar
  apply Complex.ext
  · simp [finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary,
      zeroBroadeningWeakDisorderLambda_eq_side]
    ring
  · rw [finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary]
    simp [finiteCutoffContinuumBornDenominatorIntegralBoundaryValue_im]
    rw [hgamma]
    ring

private theorem zeroBroadeningWeakDisorder_effectiveMass_eq
    (side : SpectralSide)
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0) :
    finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary
        side v m probeEnergy disorderStrength hbar pMax =
      ((m *
          (1 + zeroBroadeningWeakDisorderLambda
            v m probeEnergy disorderStrength hbar pMax) : ℝ) : ℂ) -
        ((side.sign * m *
          continuumBornDampingScale v disorderStrength hbar : ℝ) : ℂ) * Complex.I := by
  have hgamma := continuumBornDampingScale_eq_selfEnergyPrefactor
    v disorderStrength hbar hvelocity hhbar
  apply Complex.ext
  · simp [finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary,
      zeroBroadeningWeakDisorderLambda_eq_side]
    ring
  · rw [finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary]
    simp [finiteCutoffContinuumBornDenominatorIntegralBoundaryValue_im]
    rw [hgamma]
    ring

private theorem zeroBroadeningWeakDisorder_denominator_eq
    (side : SpectralSide)
    (v m p probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0) :
    finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
        side v m p probeEnergy disorderStrength hbar pMax =
      (zeroBroadeningWeakDisorderCenter
          v m p probeEnergy disorderStrength hbar pMax : ℂ) +
        ((side.sign * zeroBroadeningWeakDisorderWidth
          v m probeEnergy disorderStrength hbar pMax : ℝ) : ℂ) * Complex.I := by
  rw [finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary,
    zeroBroadeningWeakDisorder_effectiveEnergy_eq side
      v m probeEnergy disorderStrength hbar pMax hvelocity hhbar,
    zeroBroadeningWeakDisorder_effectiveMass_eq side
      v m probeEnergy disorderStrength hbar pMax hvelocity hhbar]
  cases side <;>
    simp [zeroBroadeningWeakDisorderCenter, zeroBroadeningWeakDisorderWidth,
      zeroBroadeningWeakDisorderBracket, SpectralSide.sign, pow_two] <;>
    ring

private theorem zeroBroadeningWeakDisorder_denominatorProduct_eq
    (v m p probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary
        v m p probeEnergy disorderStrength hbar pMax =
      ((zeroBroadeningWeakDisorderCenter
          v m p probeEnergy disorderStrength hbar pMax ^ 2 +
        zeroBroadeningWeakDisorderWidth
          v m probeEnergy disorderStrength hbar pMax ^ 2 : ℝ) : ℂ) := by
  rw [finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary,
    zeroBroadeningWeakDisorder_denominator_eq .retarded
      v m p probeEnergy disorderStrength hbar pMax hvelocity hhbar,
    zeroBroadeningWeakDisorder_denominator_eq .advanced
      v m p probeEnergy disorderStrength hbar pMax hvelocity hhbar]
  simp [SpectralSide.sign, pow_two]
  ring

private theorem zeroBroadeningWeakDisorder_angularNumerator_eq
    (output : Direction2)
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0) :
    finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumeratorZeroBroadeningBoundary
        output .x v m probeEnergy disorderStrength hbar pMax =
      (zeroBroadeningWeakDisorderNumerator
        output v m probeEnergy disorderStrength hbar pMax : ℂ) := by
  rw [finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumeratorZeroBroadeningBoundary,
    zeroBroadeningWeakDisorder_effectiveEnergy_eq .retarded
      v m probeEnergy disorderStrength hbar pMax hvelocity hhbar,
    zeroBroadeningWeakDisorder_effectiveEnergy_eq .advanced
      v m probeEnergy disorderStrength hbar pMax hvelocity hhbar,
    zeroBroadeningWeakDisorder_effectiveMass_eq .retarded
      v m probeEnergy disorderStrength hbar pMax hvelocity hhbar,
    zeroBroadeningWeakDisorder_effectiveMass_eq .advanced
      v m probeEnergy disorderStrength hbar pMax hvelocity hhbar]
  cases output <;>
    simp [zeroBroadeningWeakDisorderNumerator,
      inPlaneRotationCoefficient, inPlaneRotationMatrix, SpectralSide.sign] <;>
    ring

private theorem zeroBroadeningWeakDisorderBracket_pos
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hmetal : |m| < probeEnergy)
    (hrenorm : finiteCutoffContinuumBornBoundaryRealRenormalization
      v m probeEnergy disorderStrength hbar pMax < 1) :
    0 < zeroBroadeningWeakDisorderBracket
      v m probeEnergy disorderStrength hbar pMax := by
  have hmetalSq : m ^ 2 < probeEnergy ^ 2 := by
    rw [← sq_abs m]
    nlinarith [abs_nonneg m]
  have hdelta : 0 < probeEnergy ^ 2 - m ^ 2 := sub_pos.mpr hmetalSq
  have hlambdaGap :
      zeroBroadeningWeakDisorderLambda
          v m probeEnergy disorderStrength hbar pMax * (probeEnergy ^ 2 - m ^ 2) <
        probeEnergy ^ 2 - m ^ 2 := by
    exact mul_lt_mul_of_pos_right hrenorm hdelta
  unfold zeroBroadeningWeakDisorderBracket
  nlinarith [sq_nonneg m]

private theorem zeroBroadeningWeakDisorderWidth_pos
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0) (hdisorder : 0 < disorderStrength)
    (hmetal : |m| < probeEnergy)
    (hrenorm : finiteCutoffContinuumBornBoundaryRealRenormalization
      v m probeEnergy disorderStrength hbar pMax < 1) :
    0 < zeroBroadeningWeakDisorderWidth
      v m probeEnergy disorderStrength hbar pMax := by
  have hgamma : 0 < continuumBornDampingScale v disorderStrength hbar := by
    unfold continuumBornDampingScale
    have hden : 0 < 4 * hbar ^ 2 * v ^ 2 := by
      exact mul_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero hhbar))
        (sq_pos_of_ne_zero hvelocity)
    exact div_pos hdisorder hden
  unfold zeroBroadeningWeakDisorderWidth
  exact mul_pos (mul_pos (by norm_num) hgamma)
    (zeroBroadeningWeakDisorderBracket_pos
      v m probeEnergy disorderStrength hbar pMax hmetal hrenorm)

private theorem zeroBroadeningWeakDisorderCenter_eq
    (v m p probeEnergy disorderStrength hbar pMax : ℝ) :
    zeroBroadeningWeakDisorderCenter
        v m p probeEnergy disorderStrength hbar pMax =
      zeroBroadeningWeakDisorderCenter
          v m 0 probeEnergy disorderStrength hbar pMax - v ^ 2 * p ^ 2 := by
  simp [zeroBroadeningWeakDisorderCenter]
  ring

private theorem finiteCutoffContinuumBornDysonCurrentRungZeroBroadeningBoundary_eq_arctan
    (output : Direction2)
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hpMax : 0 ≤ pMax) (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hdisorder : 0 < disorderStrength) (hmetal : |m| < probeEnergy)
    (hrenorm : finiteCutoffContinuumBornBoundaryRealRenormalization
      v m probeEnergy disorderStrength hbar pMax < 1) :
    finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficientZeroBroadeningBoundary
        output .x v m probeEnergy disorderStrength hbar pMax =
      (((zeroBroadeningWeakDisorderNumerator
          output v m probeEnergy disorderStrength hbar pMax /
          (2 * Real.pi * zeroBroadeningWeakDisorderBracket
            v m probeEnergy disorderStrength hbar pMax)) *
        (Real.arctan
            (zeroBroadeningWeakDisorderCenter
              v m 0 probeEnergy disorderStrength hbar pMax /
              zeroBroadeningWeakDisorderWidth
                v m probeEnergy disorderStrength hbar pMax) -
          Real.arctan
            (zeroBroadeningWeakDisorderCenter
              v m pMax probeEnergy disorderStrength hbar pMax /
              zeroBroadeningWeakDisorderWidth
                v m probeEnergy disorderStrength hbar pMax)) : ℝ) : ℂ) := by
  let A := zeroBroadeningWeakDisorderCenter
    v m 0 probeEnergy disorderStrength hbar pMax
  let B := zeroBroadeningWeakDisorderWidth
    v m probeEnergy disorderStrength hbar pMax
  let Q := zeroBroadeningWeakDisorderBracket
    v m probeEnergy disorderStrength hbar pMax
  let numerator := zeroBroadeningWeakDisorderNumerator
    output v m probeEnergy disorderStrength hbar pMax
  let pref := disorderStrength * momentumMeasurePrefactor hbar
  have hBpos : 0 < B :=
    zeroBroadeningWeakDisorderWidth_pos
      v m probeEnergy disorderStrength hbar pMax
      hvelocity hhbar hdisorder hmetal hrenorm
  have hB : B ≠ 0 := ne_of_gt hBpos
  have hQpos : 0 < Q :=
    zeroBroadeningWeakDisorderBracket_pos
      v m probeEnergy disorderStrength hbar pMax hmetal hrenorm
  have hQ : Q ≠ 0 := ne_of_gt hQpos
  have hgamma : continuumBornDampingScale v disorderStrength hbar ≠ 0 := by
    have := zeroBroadeningWeakDisorderWidth_pos
      v m probeEnergy disorderStrength hbar pMax
      hvelocity hhbar hdisorder hmetal hrenorm
    intro hzero
    simp [zeroBroadeningWeakDisorderWidth, hzero] at this
  have hpref :
      pref = continuumBornDampingScale v disorderStrength hbar * v ^ 2 / Real.pi ^ 2 := by
    simpa [pref, continuumBornRetardedAdvancedCurrentRungPrefactor] using
      continuumBornRetardedAdvancedCurrentRungPrefactor_eq_dampingScale
        v disorderStrength hbar hvelocity hhbar
  have hcenter (p : ℝ) :
      zeroBroadeningWeakDisorderCenter
          v m p probeEnergy disorderStrength hbar pMax = A - v ^ 2 * p ^ 2 := by
    simpa [A] using
      zeroBroadeningWeakDisorderCenter_eq
        v m p probeEnergy disorderStrength hbar pMax
  have hintegrand (p : ℝ) :
      finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrandZeroBroadeningBoundary
          output .x v m p probeEnergy disorderStrength hbar pMax =
        ((((2 * Real.pi * pref * numerator) *
          (p / ((A - v ^ 2 * p ^ 2) ^ 2 + B ^ 2)) : ℝ)) : ℂ) := by
    unfold finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrandZeroBroadeningBoundary
    rw [zeroBroadeningWeakDisorder_denominatorProduct_eq
      v m p probeEnergy disorderStrength hbar pMax hvelocity hhbar,
      zeroBroadeningWeakDisorder_angularNumerator_eq
        output v m probeEnergy disorderStrength hbar pMax hvelocity hhbar,
      hcenter]
    dsimp [B, numerator, pref]
    push_cast
    simp [div_eq_mul_inv]
    ring
  have hcast :
      (∫ p in (0 : ℝ)..pMax,
        ((p / ((A - v ^ 2 * p ^ 2) ^ 2 + B ^ 2) : ℝ) : ℂ)) =
        ((∫ p in (0 : ℝ)..pMax,
          p / ((A - v ^ 2 * p ^ 2) ^ 2 + B ^ 2)) : ℂ) := by
    rw [intervalIntegral.integral_of_le hpMax, intervalIntegral.integral_of_le hpMax]
    exact integral_ofReal.symm
  have hradial :=
    integral_radialQuadraticLorentzian_eq_arctan
      v A B pMax hvelocity hB
  have hphase :
      Real.arctan ((v ^ 2 * pMax ^ 2 - A) / B) + Real.arctan (A / B) =
        Real.arctan (A / B) -
          Real.arctan
            (zeroBroadeningWeakDisorderCenter
              v m pMax probeEnergy disorderStrength hbar pMax / B) := by
    have hmax :
        (v ^ 2 * pMax ^ 2 - A) / B =
          -(zeroBroadeningWeakDisorderCenter
              v m pMax probeEnergy disorderStrength hbar pMax / B) := by
      rw [hcenter]
      ring
    rw [hmax, Real.arctan_neg]
    ring
  have hscale :
      (2 * Real.pi * pref * numerator) * (2 * v ^ 2 * B)⁻¹ =
        numerator / (2 * Real.pi * Q) := by
    rw [hpref]
    dsimp [B, Q]
    field_simp [hvelocity, hgamma, hQ, Real.pi_ne_zero]
    ring
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficientZeroBroadeningBoundary
  simp_rw [hintegrand]
  rw [show
      (fun p : ℝ =>
        ((((2 * Real.pi * pref * numerator) *
          (p / ((A - v ^ 2 * p ^ 2) ^ 2 + B ^ 2)) : ℝ)) : ℂ)) =
      (fun p : ℝ =>
        ((2 * Real.pi * pref * numerator : ℝ) : ℂ) *
          ((p / ((A - v ^ 2 * p ^ 2) ^ 2 + B ^ 2) : ℝ) : ℂ)) by
    funext p
    push_cast
    ring]
  rw [intervalIntegral.integral_const_mul, hcast, hradial]
  push_cast
  rw [hphase]
  push_cast at hscale
  rw [hscale]
  dsimp [A, B, Q, numerator]
  ring

private theorem tendsto_zeroBroadeningWeakDisorderLambda_disorder_zero
    (v m probeEnergy hbar pMax : ℝ) :
    Tendsto
      (fun disorderStrength : ℝ =>
        zeroBroadeningWeakDisorderLambda
          v m probeEnergy disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hcont : ContinuousAt
      (fun disorderStrength : ℝ =>
        zeroBroadeningWeakDisorderLambda
          v m probeEnergy disorderStrength hbar pMax) 0 := by
    unfold zeroBroadeningWeakDisorderLambda
      finiteCutoffContinuumBornBoundaryRealRenormalization
    fun_prop
  simpa [zeroBroadeningWeakDisorderLambda,
    finiteCutoffContinuumBornBoundaryRealRenormalization] using
    hcont.tendsto.mono_left inf_le_left

private theorem eventually_zeroBroadeningWeakDisorderLambda_lt_one
    (v m probeEnergy hbar pMax : ℝ) :
    ∀ᶠ disorderStrength : ℝ in nhdsWithin 0 (Set.Ioi 0),
      zeroBroadeningWeakDisorderLambda
        v m probeEnergy disorderStrength hbar pMax < 1 :=
  (tendsto_zeroBroadeningWeakDisorderLambda_disorder_zero
    v m probeEnergy hbar pMax).eventually (Iio_mem_nhds (by norm_num))

private theorem tendsto_zeroBroadeningWeakDisorderCenter_disorder_zero
    (v m p probeEnergy hbar pMax : ℝ) :
    Tendsto
      (fun disorderStrength : ℝ =>
        zeroBroadeningWeakDisorderCenter
          v m p probeEnergy disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (probeEnergy ^ 2 - m ^ 2 - v ^ 2 * p ^ 2)) := by
  have hcont : ContinuousAt
      (fun disorderStrength : ℝ =>
        zeroBroadeningWeakDisorderCenter
          v m p probeEnergy disorderStrength hbar pMax) 0 := by
    unfold zeroBroadeningWeakDisorderCenter zeroBroadeningWeakDisorderLambda
      finiteCutoffContinuumBornBoundaryRealRenormalization continuumBornDampingScale
    fun_prop
  simpa [zeroBroadeningWeakDisorderCenter, zeroBroadeningWeakDisorderLambda,
    finiteCutoffContinuumBornBoundaryRealRenormalization, continuumBornDampingScale] using
    hcont.tendsto.mono_left inf_le_left

private theorem tendsto_zeroBroadeningWeakDisorderWidth_disorder_zero
    (v m probeEnergy hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0) (hmetal : |m| < probeEnergy) :
    Tendsto
      (fun disorderStrength : ℝ =>
        zeroBroadeningWeakDisorderWidth
          v m probeEnergy disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin 0 (Set.Ioi 0)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hcont : ContinuousAt
        (fun disorderStrength : ℝ =>
          zeroBroadeningWeakDisorderWidth
            v m probeEnergy disorderStrength hbar pMax) 0 := by
      unfold zeroBroadeningWeakDisorderWidth zeroBroadeningWeakDisorderBracket
        zeroBroadeningWeakDisorderLambda finiteCutoffContinuumBornBoundaryRealRenormalization
        continuumBornDampingScale
      fun_prop
    simpa [zeroBroadeningWeakDisorderWidth, zeroBroadeningWeakDisorderBracket,
      zeroBroadeningWeakDisorderLambda, finiteCutoffContinuumBornBoundaryRealRenormalization,
      continuumBornDampingScale] using hcont.tendsto.mono_left inf_le_left
  · filter_upwards [self_mem_nhdsWithin,
      eventually_zeroBroadeningWeakDisorderLambda_lt_one
        v m probeEnergy hbar pMax] with disorderStrength hdisorder hlambda
    exact zeroBroadeningWeakDisorderWidth_pos
      v m probeEnergy disorderStrength hbar pMax
      hvelocity hhbar hdisorder hmetal hlambda

private theorem tendsto_zeroBroadeningWeakDisorderPrefactor_disorder_zero
    (output : Direction2) (v m probeEnergy hbar pMax : ℝ)
    (hmetal : |m| < probeEnergy) :
    Tendsto
      (fun disorderStrength : ℝ =>
        zeroBroadeningWeakDisorderNumerator
            output v m probeEnergy disorderStrength hbar pMax /
          (2 * Real.pi * zeroBroadeningWeakDisorderBracket
            v m probeEnergy disorderStrength hbar pMax))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (zeroBroadeningWeakDisorderPrefactorTarget output m probeEnergy)) := by
  have hprobe : 0 < probeEnergy := lt_of_le_of_lt (abs_nonneg m) hmetal
  have hsum : 0 < probeEnergy ^ 2 + m ^ 2 := by
    nlinarith [sq_pos_of_ne_zero (ne_of_gt hprobe), sq_nonneg m]
  cases output <;>
    have hcont : ContinuousAt
        (fun disorderStrength : ℝ =>
          zeroBroadeningWeakDisorderNumerator
              _ v m probeEnergy disorderStrength hbar pMax /
            (2 * Real.pi * zeroBroadeningWeakDisorderBracket
              v m probeEnergy disorderStrength hbar pMax)) 0 := by
      unfold zeroBroadeningWeakDisorderNumerator zeroBroadeningWeakDisorderBracket
        zeroBroadeningWeakDisorderLambda finiteCutoffContinuumBornBoundaryRealRenormalization
        continuumBornDampingScale
      fun_prop
    simpa [zeroBroadeningWeakDisorderNumerator, zeroBroadeningWeakDisorderBracket,
      zeroBroadeningWeakDisorderLambda, zeroBroadeningWeakDisorderPrefactorTarget,
      finiteCutoffContinuumBornBoundaryRealRenormalization, continuumBornDampingScale] using
      hcont.tendsto.mono_left inf_le_left

/-- At fixed cutoff beyond the metallic shell, the canonical zero-broadening source-`.x`
Born-Dyson current rung converges as a single in-plane coefficient vector to `(κ, 0)`. -/
theorem tendsto_finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary_disorder_zero
    (v m probeEnergy hbar pMax : ℝ)
    (hpMax : 0 ≤ pMax) (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun disorderStrength output =>
        finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficientZeroBroadeningBoundary
          output .x v m probeEnergy disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (inPlaneCoefficientVector
          (continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
            m probeEnergy : ℂ) 0)) := by
  have hdelta : 0 < probeEnergy ^ 2 - m ^ 2 := by
    rw [← sq_abs m]
    nlinarith [abs_nonneg m]
  have hcenter0 :=
    tendsto_zeroBroadeningWeakDisorderCenter_disorder_zero
      v m 0 probeEnergy hbar pMax
  have hcenterMax :=
    tendsto_zeroBroadeningWeakDisorderCenter_disorder_zero
      v m pMax probeEnergy hbar pMax
  have hcenterMaxNeg :
      probeEnergy ^ 2 - m ^ 2 - v ^ 2 * pMax ^ 2 < 0 := by
    linarith
  have hwidth :=
    tendsto_zeroBroadeningWeakDisorderWidth_disorder_zero
      v m probeEnergy hbar pMax hvelocity hhbar hmetal
  have hphase : Tendsto
      (fun disorderStrength : ℝ =>
        Real.arctan
            (zeroBroadeningWeakDisorderCenter
              v m 0 probeEnergy disorderStrength hbar pMax /
              zeroBroadeningWeakDisorderWidth
                v m probeEnergy disorderStrength hbar pMax) -
          Real.arctan
            (zeroBroadeningWeakDisorderCenter
              v m pMax probeEnergy disorderStrength hbar pMax /
              zeroBroadeningWeakDisorderWidth
                v m probeEnergy disorderStrength hbar pMax))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds Real.pi) :=
    tendsto_arctan_div_sub_arctan_div_nhdsGT_zero
      hcenter0 hdelta hcenterMax hcenterMaxNeg hwidth
  rw [tendsto_pi_nhds]
  intro output
  have hpref :=
    tendsto_zeroBroadeningWeakDisorderPrefactor_disorder_zero
      output v m probeEnergy hbar pMax hmetal
  have hclosed := (hpref.mul hphase).ofReal
  have htarget :
      (zeroBroadeningWeakDisorderPrefactorTarget output m probeEnergy * Real.pi : ℂ) =
        inPlaneCoefficientVector
          (continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
            m probeEnergy : ℂ) 0 output := by
    have hprobe : 0 < probeEnergy := lt_of_le_of_lt (abs_nonneg m) hmetal
    have hsum : probeEnergy ^ 2 + m ^ 2 ≠ 0 := by
      nlinarith [sq_pos_of_ne_zero (ne_of_gt hprobe), sq_nonneg m]
    cases output
    · simp [zeroBroadeningWeakDisorderPrefactorTarget, inPlaneCoefficientVector]
      unfold continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
      push_cast
      field_simp [Real.pi_ne_zero, hsum]
      ring
    · simp [zeroBroadeningWeakDisorderPrefactorTarget, inPlaneCoefficientVector]
  rw [htarget] at hclosed
  apply Tendsto.congr' ?_ hclosed
  filter_upwards [self_mem_nhdsWithin,
      eventually_zeroBroadeningWeakDisorderLambda_lt_one
        v m probeEnergy hbar pMax] with disorderStrength hdisorder hlambda
  exact
    (finiteCutoffContinuumBornDysonCurrentRungZeroBroadeningBoundary_eq_arctan
      output v m probeEnergy disorderStrength hbar pMax hpMax hvelocity hhbar
      hdisorder hmetal hlambda).symm

end

end QuantumTheory.Transport.Models.MassiveDirac
