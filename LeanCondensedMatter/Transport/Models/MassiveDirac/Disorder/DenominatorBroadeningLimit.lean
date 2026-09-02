import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.DenominatorEvaluation
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Zero-broadening limit of the continuum Born denominator imaginary part

At fixed finite cutoff in the positive-mass metallic regime `0 < m < ε`, this file proves the
positive-broadening limit of the imaginary part of the shared continuum Born denominator integral.
When `ε² - m² < v² pMax²`, the retarded cutoff denominator approaches the negative-real branch cut
from above and the advanced denominator from below. Hence `Im J_R → -π/(2v²)` and
`Im J_A → +π/(2v²)`. No simultaneous UV limit or scattering-rate identification is made.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter
open QuantumTheory.Transport

private theorem tendsto_pauliGreenDenominator_radial_broadening_zero
    (side : SpectralSide) (v m probeEnergy p : ℝ) :
    Tendsto
      (fun broadening : ℝ => pauliGreenDenominator side v m p 0 probeEnergy broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (pauliGreenDenominator side v m p 0 probeEnergy 0)) := by
  have hcontinuous :
      ContinuousAt
        (fun broadening : ℝ => pauliGreenDenominator side v m p 0 probeEnergy broadening) 0 := by
    unfold pauliGreenDenominator energySq spectralParameter spectralParameterOfRegulator
    fun_prop
  exact hcontinuous.tendsto.mono_left inf_le_left

private theorem tendsto_arg_pauliGreenDenominator_zero_radial_broadening_zero
    (side : SpectralSide) (v m probeEnergy : ℝ)
    (hm : 0 < m) (hmE : m < probeEnergy) :
    Tendsto
      (fun broadening : ℝ =>
        (pauliGreenDenominator side v m 0 0 probeEnergy broadening).arg)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hre : 0 < (pauliGreenDenominator side v m 0 0 probeEnergy 0).re := by
    rw [pauliGreenDenominator_radial_re]
    nlinarith
  have him : (pauliGreenDenominator side v m 0 0 probeEnergy 0).im = 0 := by
    rw [pauliGreenDenominator_radial_im]
    simp
  have hslit : pauliGreenDenominator side v m 0 0 probeEnergy 0 ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    exact Or.inl hre
  have harg :=
    (Complex.continuousAt_arg hslit).tendsto.comp
      (tendsto_pauliGreenDenominator_radial_broadening_zero side v m probeEnergy 0)
  have hargZero : (pauliGreenDenominator side v m 0 0 probeEnergy 0).arg = 0 := by
    rw [Complex.arg_eq_zero_iff]
    exact ⟨hre.le, him⟩
  rw [hargZero] at harg
  exact harg

private theorem tendsto_arg_pauliGreenDenominator_cutoff_broadening_zero
    (side : SpectralSide) (v m probeEnergy pMax : ℝ)
    (hm : 0 < m) (hmE : m < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        (pauliGreenDenominator side v m pMax 0 probeEnergy broadening).arg)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (side.sign * Real.pi)) := by
  have henergy : 0 < probeEnergy := lt_trans hm hmE
  have hre : (pauliGreenDenominator side v m pMax 0 probeEnergy 0).re < 0 := by
    rw [pauliGreenDenominator_radial_re]
    nlinarith
  have him : (pauliGreenDenominator side v m pMax 0 probeEnergy 0).im = 0 := by
    rw [pauliGreenDenominator_radial_im]
    simp
  have hden := tendsto_pauliGreenDenominator_radial_broadening_zero
    side v m probeEnergy pMax
  cases side with
  | retarded =>
      have hwithin :
          Tendsto
            (fun broadening : ℝ =>
              pauliGreenDenominator .retarded v m pMax 0 probeEnergy broadening)
            (nhdsWithin 0 (Set.Ioi 0))
            (nhdsWithin
              (pauliGreenDenominator .retarded v m pMax 0 probeEnergy 0)
              {z : ℂ | 0 ≤ z.im}) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨hden, ?_⟩
        filter_upwards [self_mem_nhdsWithin] with broadening hbroadening
        rw [pauliGreenDenominator_radial_im]
        simp only [SpectralSide.sign_retarded]
        nlinarith [mul_pos henergy hbroadening]
      have harg :=
        (Complex.tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero hre him).comp hwithin
      simpa [Function.comp_def, SpectralSide.sign] using harg
  | advanced =>
      have hwithin :
          Tendsto
            (fun broadening : ℝ =>
              pauliGreenDenominator .advanced v m pMax 0 probeEnergy broadening)
            (nhdsWithin 0 (Set.Ioi 0))
            (nhdsWithin
              (pauliGreenDenominator .advanced v m pMax 0 probeEnergy 0)
              {z : ℂ | z.im < 0}) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨hden, ?_⟩
        filter_upwards [self_mem_nhdsWithin] with broadening hbroadening
        rw [pauliGreenDenominator_radial_im]
        simp only [SpectralSide.sign_advanced]
        nlinarith [mul_pos henergy hbroadening]
      have harg :=
        (Complex.tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero hre him).comp hwithin
      simpa [Function.comp_def, SpectralSide.sign] using harg

/-- At fixed finite cutoff beyond the on-shell circle, `Im J_s → -sπ/(2v²)` as `η → 0⁺`. -/
theorem tendsto_finiteCutoffContinuumBornDenominatorIntegral_im_broadening_zero
    (side : SpectralSide) (v m probeEnergy pMax : ℝ)
    (hvelocity : v ≠ 0) (hm : 0 < m) (hmE : m < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        (finiteCutoffContinuumBornDenominatorIntegral
          side v m probeEnergy broadening pMax).im)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (-(((2 : ℝ) * v ^ 2)⁻¹) * (side.sign * Real.pi))) := by
  have hprobeEnergy : probeEnergy ≠ 0 := ne_of_gt (lt_trans hm hmE)
  have hargCutoff := tendsto_arg_pauliGreenDenominator_cutoff_broadening_zero
    side v m probeEnergy pMax hm hmE hcutoff
  have hargZero := tendsto_arg_pauliGreenDenominator_zero_radial_broadening_zero
    side v m probeEnergy hm hmE
  have hdiff :
      Tendsto
        (fun broadening : ℝ =>
          (pauliGreenDenominator side v m pMax 0 probeEnergy broadening).arg -
            (pauliGreenDenominator side v m 0 0 probeEnergy broadening).arg)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (side.sign * Real.pi)) := by
    simpa using hargCutoff.sub hargZero
  refine ((tendsto_const_nhds : Tendsto
    (fun _ : ℝ => -(((2 : ℝ) * v ^ 2)⁻¹))
    (nhdsWithin 0 (Set.Ioi 0))
    (nhds (-(((2 : ℝ) * v ^ 2)⁻¹)))).mul hdiff).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with broadening hbroadening
  have hbroadening_ne : broadening ≠ 0 := ne_of_gt hbroadening
  exact (finiteCutoffContinuumBornDenominatorIntegral_im_eq
    side v m probeEnergy broadening pMax hvelocity hprobeEnergy hbroadening_ne).symm

/-- Retarded specialization: `Im J_R → -π/(2v²)`. -/
theorem tendsto_finiteCutoffContinuumBornRetardedDenominatorIntegral_im_broadening_zero
    (v m probeEnergy pMax : ℝ)
    (hvelocity : v ≠ 0) (hm : 0 < m) (hmE : m < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        (finiteCutoffContinuumBornDenominatorIntegral
          .retarded v m probeEnergy broadening pMax).im)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (-(((2 : ℝ) * v ^ 2)⁻¹) * Real.pi)) := by
  simpa [SpectralSide.sign] using
    (tendsto_finiteCutoffContinuumBornDenominatorIntegral_im_broadening_zero
      .retarded v m probeEnergy pMax hvelocity hm hmE hcutoff)

/-- Advanced specialization: `Im J_A → +π/(2v²)`. -/
theorem tendsto_finiteCutoffContinuumBornAdvancedDenominatorIntegral_im_broadening_zero
    (v m probeEnergy pMax : ℝ)
    (hvelocity : v ≠ 0) (hm : 0 < m) (hmE : m < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        (finiteCutoffContinuumBornDenominatorIntegral
          .advanced v m probeEnergy broadening pMax).im)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (((2 : ℝ) * v ^ 2)⁻¹ * Real.pi)) := by
  simpa [SpectralSide.sign] using
    (tendsto_finiteCutoffContinuumBornDenominatorIntegral_im_broadening_zero
      .advanced v m probeEnergy pMax hvelocity hm hmE hcutoff)

end

end AnomalousHall.MassiveDirac
