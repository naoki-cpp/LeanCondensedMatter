import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderLongitudinalZeroBroadeningIntegral
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningLadderZeroBroadeningWeakDisorder
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Weak-disorder limit of the zero-broadening longitudinal Středa momentum integral

The zero-broadening boundary is formed first at fixed disorder. This module then takes the separate
one-sided `W → 0⁺` limit after multiplying the longitudinal momentum integral by `W`. The singular
retarded-advanced term is controlled by the canonical ladder-action limit, while the same-side
endpoint terms remain finite and therefore vanish after multiplication by `W`.

The cutoff remains fixed beyond the metallic shell. Physical conductivity normalization remains
owned downstream by `MassiveDirac.Conductivity`.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter QuantumTheory.Transport

/-- After the fixed-cutoff zero-broadening boundary is formed, multiplying the longitudinal Středa
momentum integral by the disorder strength gives a finite weak-disorder limit. -/
theorem tendsto_disorderStrength_mul_finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceMomentumIntegralZeroBroadeningBoundary_disorder_zero
    (e v m probeEnergy hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun disorderStrength : ℝ =>
        (disorderStrength : ℂ) *
          finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceMomentumIntegralZeroBroadeningBoundary
            e v m probeEnergy disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (2 * ((((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))) ^ 2 *
          (((momentumMeasurePrefactor hbar : ℝ) : ℂ))⁻¹ *
          (((probeEnergy ^ 2 - m ^ 2) /
            (probeEnergy ^ 2 + 3 * m ^ 2) : ℝ) : ℂ))) := by
  let l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  let q : ℂ := (((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))
  let measure : ℂ := ((momentumMeasurePrefactor hbar : ℝ) : ℂ)
  let endpoint : SpectralSide → ℝ → ℂ := fun side disorderStrength =>
    ((((2 * v ^ 2 : ℝ) : ℂ))⁻¹ *
        (finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary
            side v m probeEnergy disorderStrength hbar pMax ^ 2 -
          finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary
            side v m probeEnergy disorderStrength hbar pMax ^ 2)) *
      ((finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
          side v m pMax probeEnergy disorderStrength hbar pMax)⁻¹ -
        (finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
          side v m 0 probeEnergy disorderStrength hbar pMax)⁻¹)
  have hl : l ≤ nhds 0 := by
    dsimp [l, nhdsWithin]
    exact inf_le_left
  have hgap : 0 < probeEnergy ^ 2 - m ^ 2 := by
    have hprobe : 0 < probeEnergy := lt_of_le_of_lt (abs_nonneg m) hmetal
    rw [← sq_abs m]
    nlinarith [abs_nonneg m]
  have hmax : probeEnergy ^ 2 - m ^ 2 - v ^ 2 * pMax ^ 2 < 0 := by
    linarith
  have hmeasureReal : momentumMeasurePrefactor hbar ≠ 0 := by
    unfold momentumMeasurePrefactor
    exact one_div_ne_zero (pow_ne_zero 2
      (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hhbar))
  have hmeasure : measure ≠ 0 := by
    dsimp [measure]
    exact_mod_cast hmeasureReal
  have hEndpoint (side : SpectralSide) : ContinuousAt (endpoint side) 0 := by
    have hden0 :
        finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
          side v m 0 probeEnergy 0 hbar pMax ≠ 0 := by
      have hreal : probeEnergy ^ 2 - m ^ 2 ≠ 0 := ne_of_gt hgap
      simpa [finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary,
        finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary,
        finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary] using
        (show (((probeEnergy ^ 2 - m ^ 2 : ℝ) : ℂ)) ≠ 0 by exact_mod_cast hreal)
    have hdenMax :
        finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
          side v m pMax probeEnergy 0 hbar pMax ≠ 0 := by
      have hreal : probeEnergy ^ 2 - m ^ 2 - v ^ 2 * pMax ^ 2 ≠ 0 := ne_of_lt hmax
      simpa [finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary,
        finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary,
        finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary] using
        (show (((probeEnergy ^ 2 - m ^ 2 - v ^ 2 * pMax ^ 2 : ℝ) : ℂ)) ≠ 0 by
          exact_mod_cast hreal)
    have hE : ContinuousAt
        (fun disorderStrength : ℝ =>
          finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary
            side v m probeEnergy disorderStrength hbar pMax) 0 := by
      unfold finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary
      fun_prop
    have hM : ContinuousAt
        (fun disorderStrength : ℝ =>
          finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary
            side v m probeEnergy disorderStrength hbar pMax) 0 := by
      unfold finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary
      fun_prop
    have hD0 : ContinuousAt
        (fun disorderStrength : ℝ =>
          finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
            side v m 0 probeEnergy disorderStrength hbar pMax) 0 := by
      unfold finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
      fun_prop
    have hDMax : ContinuousAt
        (fun disorderStrength : ℝ =>
          finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
            side v m pMax probeEnergy disorderStrength hbar pMax) 0 := by
      unfold finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
      fun_prop
    dsimp [endpoint]
    exact (continuousAt_const.mul ((hE.pow 2).sub (hM.pow 2))).mul
      ((hDMax.inv₀ hdenMax).sub (hD0.inv₀ hden0))
  have hWReal : Tendsto (fun disorderStrength : ℝ => disorderStrength) l (nhds 0) :=
    continuousAt_id.tendsto.mono_left hl
  have hW := hWReal.ofReal
  have hScaledEndpoint (side : SpectralSide) :
      Tendsto
        (fun disorderStrength : ℝ =>
          (disorderStrength : ℂ) * endpoint side disorderStrength)
        l (nhds 0) := by
    simpa using hW.mul ((hEndpoint side).tendsto.mono_left hl)
  have haction :=
    tendsto_finiteCutoffContinuumBornDysonLongitudinalLadderActionZeroBroadeningBoundary_disorder_zero
      v m probeEnergy hbar pMax hvelocity hhbar hmetal hcutoff
  have hRA := haction.const_mul (2 * q ^ 2 * measure⁻¹)
  have hSame :=
    ((hScaledEndpoint .retarded).add (hScaledEndpoint .advanced)).const_mul
      ((((2 * Real.pi : ℝ) : ℂ)) * q ^ 2)
  have hTotal := hRA.sub hSame
  simp only [add_zero, mul_zero, sub_zero] at hTotal
  apply Tendsto.congr' ?_ (by simpa [q, measure] using hTotal)
  filter_upwards [self_mem_nhdsWithin] with disorderStrength hdisorder
  have hdisorderC : (disorderStrength : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hdisorder
  have hboundary :
      finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceMomentumIntegralZeroBroadeningBoundary
          e v m probeEnergy disorderStrength hbar pMax =
        2 * q ^ 2 *
            (((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ))⁻¹ *
            inPlaneLadderAction
              (finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary
                v m probeEnergy disorderStrength hbar pMax)
              (finiteCutoffContinuumBornDysonLadderSolvedVectorZeroBroadeningBoundary
                v m probeEnergy disorderStrength hbar pMax) .x -
          (((2 * Real.pi : ℝ) : ℂ)) * q ^ 2 *
            (endpoint .retarded disorderStrength + endpoint .advanced disorderStrength) := by
    rfl
  rw [hboundary]
  simp only [inPlaneLadderAction_apply_x,
    finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary]
  push_cast
  dsimp [q, measure] at hmeasure ⊢
  push_cast
  field_simp [hdisorderC, hmeasure]

end

end QuantumTheory.Transport.Models.MassiveDirac
