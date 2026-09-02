import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.BornCurrentVertexWeakDisorder
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.TransportRate
import Mathlib.Topology.Algebra.Order.Field

set_option linter.style.header false

/-!
# Weak-disorder current-rung / transport-lifetime bridge

This module takes the exact finite-cutoff arctangent representation of the normalized Born
retarded-advanced longitudinal current rung and performs the one-sided weak-disorder limit at fixed
cutoff.  The cutoff is required to lie beyond the metallic on-shell Fermi circle, so the two
arctangent endpoints approach opposite sides of the resonance and their difference tends to `π`.

The resulting scalar rung coefficient is then connected to the already-derived microscopic
transport-to-single-particle lifetime factor.  This is still a Born current-vertex statement; no
Kubo conductivity or exact disorder-average identification is made here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter

private theorem tendsto_arctan_div_nhdsGT_zero_of_pos
    {l : Filter ℝ} {f g : ℝ → ℝ} {a : ℝ}
    (hf : Tendsto f l (nhds a)) (ha : 0 < a)
    (hg : Tendsto g l (nhdsWithin 0 (Set.Ioi 0))) :
    Tendsto (fun x => Real.arctan (f x / g x)) l (nhds (Real.pi / 2)) := by
  change Tendsto (Real.arctan ∘ fun x => f x / g x) l (nhds (Real.pi / 2))
  simpa only [div_eq_mul_inv, Function.comp_apply] using
    tendsto_nhds_of_tendsto_nhdsWithin
      (Real.tendsto_arctan_atTop.comp
        (hf.pos_mul_atTop ha (tendsto_inv_nhdsGT_zero.comp hg)))

private theorem tendsto_arctan_div_nhdsGT_zero_of_neg
    {l : Filter ℝ} {f g : ℝ → ℝ} {a : ℝ}
    (hf : Tendsto f l (nhds a)) (ha : a < 0)
    (hg : Tendsto g l (nhdsWithin 0 (Set.Ioi 0))) :
    Tendsto (fun x => Real.arctan (f x / g x)) l (nhds (-(Real.pi / 2))) := by
  change Tendsto (Real.arctan ∘ fun x => f x / g x) l (nhds (-(Real.pi / 2)))
  simpa only [div_eq_mul_inv, Function.comp_apply] using
    tendsto_nhds_of_tendsto_nhdsWithin
      (Real.tendsto_arctan_atBot.comp
        (hf.neg_mul_atTop ha (tendsto_inv_nhdsGT_zero.comp hg)))

private theorem tendsto_continuumBornRADenominatorCenter_disorder_zero
    (v m p probeEnergy hbar : ℝ) :
    Tendsto
      (fun disorderStrength : ℝ =>
        continuumBornRADenominatorCenter
          v m p probeEnergy disorderStrength hbar)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((probeEnergy ^ 2 - m ^ 2) - v ^ 2 * p ^ 2)) := by
  have hcont : ContinuousAt
      (fun disorderStrength : ℝ =>
        continuumBornRADenominatorCenter
          v m p probeEnergy disorderStrength hbar) 0 := by
    unfold continuumBornRADenominatorCenter continuumBornDampingScale
    fun_prop
  simpa [nhdsWithin, continuumBornRADenominatorCenter, continuumBornDampingScale] using
    hcont.tendsto.mono_left inf_le_left

private theorem tendsto_continuumBornRADenominatorWidth_disorder_zero
    (v m probeEnergy hbar : ℝ)
    (hv : v ≠ 0) (hhbar : 0 < hbar)
    (hsum : 0 < probeEnergy ^ 2 + m ^ 2) :
    Tendsto
      (fun disorderStrength : ℝ =>
        continuumBornRADenominatorWidth
          v m probeEnergy disorderStrength hbar)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin 0 (Set.Ioi 0)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hcont : ContinuousAt
        (fun disorderStrength : ℝ =>
          continuumBornRADenominatorWidth
            v m probeEnergy disorderStrength hbar) 0 := by
      unfold continuumBornRADenominatorWidth continuumBornDampingScale
      fun_prop
    simpa [nhdsWithin, continuumBornRADenominatorWidth, continuumBornDampingScale] using
      hcont.tendsto.mono_left inf_le_left
  · filter_upwards [self_mem_nhdsWithin] with disorderStrength hdisorder
    have hdisorderPos : 0 < disorderStrength := hdisorder
    have hgamma :
        0 < continuumBornDampingScale v disorderStrength hbar := by
      unfold continuumBornDampingScale
      have hden : 0 < 4 * hbar ^ 2 * v ^ 2 := by positivity
      exact div_pos hdisorderPos hden
    change 0 < continuumBornRADenominatorWidth
      v m probeEnergy disorderStrength hbar
    unfold continuumBornRADenominatorWidth
    positivity

private theorem tendsto_continuumBornRetardedAdvancedCurrentRungPrefactorFactor_disorder_zero
    (v m probeEnergy hbar : ℝ) :
    Tendsto
      (fun disorderStrength : ℝ =>
        (1 + continuumBornDampingScale v disorderStrength hbar ^ 2) *
          (probeEnergy ^ 2 - m ^ 2) /
          (2 * Real.pi * (probeEnergy ^ 2 + m ^ 2)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        ((probeEnergy ^ 2 - m ^ 2) /
          (2 * Real.pi * (probeEnergy ^ 2 + m ^ 2)))) := by
  have hcont : ContinuousAt
      (fun disorderStrength : ℝ =>
        (1 + continuumBornDampingScale v disorderStrength hbar ^ 2) *
          (probeEnergy ^ 2 - m ^ 2) /
          (2 * Real.pi * (probeEnergy ^ 2 + m ^ 2))) 0 := by
    unfold continuumBornDampingScale
    fun_prop
  simpa [nhdsWithin, continuumBornDampingScale] using
    hcont.tendsto.mono_left inf_le_left

/-- At fixed cutoff beyond the metallic on-shell circle, the fully normalized Born RA longitudinal
`σₓ` current rung has a finite one-sided weak-disorder limit.

The cutoff condition
`probeEnergy² - m² < v² pMax²`
is exactly what forces the two arctangent endpoints to lie on opposite sides of the resonance as
the disorder broadening vanishes. -/
theorem tendsto_finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungXCoefficient_disorder_zero
    (v m probeEnergy hbar pMax : ℝ)
    (hv : v ≠ 0) (hhbar : 0 < hbar)
    (hm : 0 < m) (hmF : m < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun disorderStrength : ℝ =>
        finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungXCoefficient
          v m probeEnergy disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
          m probeEnergy)) := by
  have hprobe : 0 < probeEnergy := lt_trans hm hmF
  have hdelta : 0 < probeEnergy ^ 2 - m ^ 2 := by
    have hprod : 0 < (probeEnergy - m) * (probeEnergy + m) :=
      mul_pos (sub_pos.mpr hmF) (add_pos hprobe hm)
    nlinarith
  have hsum : 0 < probeEnergy ^ 2 + m ^ 2 := by positivity
  have hsumNe : probeEnergy ^ 2 + m ^ 2 ≠ 0 := ne_of_gt hsum
  have hwidth :=
    tendsto_continuumBornRADenominatorWidth_disorder_zero
      v m probeEnergy hbar hv hhbar hsum
  have hcenter0 : Tendsto
      (fun disorderStrength : ℝ =>
        continuumBornRADenominatorCenter
          v m 0 probeEnergy disorderStrength hbar)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (probeEnergy ^ 2 - m ^ 2)) := by
    simpa using
      (tendsto_continuumBornRADenominatorCenter_disorder_zero
        v m 0 probeEnergy hbar)
  have hphase0 : Tendsto
      (fun disorderStrength : ℝ =>
        continuumBornRetardedAdvancedCurrentRungArctanPhase
          v m 0 probeEnergy disorderStrength hbar)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Real.pi / 2)) := by
    simpa [continuumBornRetardedAdvancedCurrentRungArctanPhase] using
      (tendsto_arctan_div_nhdsGT_zero_of_pos hcenter0 hdelta hwidth)
  have hcenterMax :=
    tendsto_continuumBornRADenominatorCenter_disorder_zero
      v m pMax probeEnergy hbar
  have hcenterMaxNeg :
      probeEnergy ^ 2 - m ^ 2 - v ^ 2 * pMax ^ 2 < 0 := by
    linarith
  have hphaseMax : Tendsto
      (fun disorderStrength : ℝ =>
        continuumBornRetardedAdvancedCurrentRungArctanPhase
          v m pMax probeEnergy disorderStrength hbar)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (-(Real.pi / 2))) := by
    simpa [continuumBornRetardedAdvancedCurrentRungArctanPhase] using
      (tendsto_arctan_div_nhdsGT_zero_of_neg
        hcenterMax hcenterMaxNeg hwidth)
  have hphaseDiff := hphase0.sub hphaseMax
  have hpref :=
    tendsto_continuumBornRetardedAdvancedCurrentRungPrefactorFactor_disorder_zero
      v m probeEnergy hbar
  have hclosed := hpref.mul hphaseDiff
  have htarget :
      ((probeEnergy ^ 2 - m ^ 2) /
          (2 * Real.pi * (probeEnergy ^ 2 + m ^ 2))) *
        (Real.pi / 2 - (-(Real.pi / 2))) =
      continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
        m probeEnergy := by
    unfold continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
    field_simp [Real.pi_ne_zero, hsumNe]
    ring
  rw [htarget] at hclosed
  apply Tendsto.congr' ?_ hclosed
  filter_upwards [self_mem_nhdsWithin] with disorderStrength hdisorder
  exact
    (finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungXCoefficient_eq_arctan_normalized
      v m probeEnergy disorderStrength hbar pMax hv (ne_of_gt hhbar)
      (ne_of_gt hdisorder) hsumNe).symm

/-- The scalar ladder factor extracted from the weak-disorder normalized current rung is exactly the
factor already derived algebraically between the Born transport and single-particle lifetimes. -/
theorem continuumBornUpperBandTransportLifetime_eq_weakDisorderCurrentRungFactor_mul_singleParticleLifetime
    (v m fermiEnergy disorderStrength hbar : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0) (hdisorder : disorderStrength ≠ 0)
    (hfermiEnergy : fermiEnergy ≠ 0) :
    continuumBornUpperBandTransportLifetime
        v m fermiEnergy disorderStrength hbar =
      (1 - continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
          m fermiEnergy)⁻¹ *
        continuumBornUpperBandSingleParticleLifetime
          v m fermiEnergy disorderStrength hbar := by
  rw [continuumBornUpperBandTransportLifetime_eq_factor_mul_singleParticleLifetime
    v m fermiEnergy disorderStrength hbar hvelocity hhbar hdisorder hfermiEnergy]
  have hfermiSq : 0 < fermiEnergy ^ 2 := sq_pos_of_ne_zero hfermiEnergy
  have hden : fermiEnergy ^ 2 + 3 * m ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg hfermiSq
      (mul_nonneg (by norm_num) (sq_nonneg m)))
  rw [inv_one_sub_continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
    m fermiEnergy hden]

end

end AnomalousHall.MassiveDirac
