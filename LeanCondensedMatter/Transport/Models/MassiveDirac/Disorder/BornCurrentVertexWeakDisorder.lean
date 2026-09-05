import LeanCondensedMatter.Analysis.Lorentzian.RadialQuadratic
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.BornCurrentVertexFiniteCutoff
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.TransportRate
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Weak-disorder longitudinal Born current rung

This module starts from the finite-cutoff Born-dressed `Gᴿ σₓ Gᴬ` radial kernel, attaches the
external scalar-disorder line and physical momentum measure, evaluates the normalized longitudinal
coefficient exactly, and then takes the one-sided weak-disorder limit at fixed cutoff.  The cutoff
is required to lie beyond the metallic on-shell Fermi circle so the two arctangent endpoints
approach opposite sides of the resonance.

The resulting scalar rung coefficient is connected to the microscopic transport-to-single-particle
lifetime factor.  This remains a Born current-vertex result; no Kubo conductivity or exact
disorder-average identification is made here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open MeasureTheory
open Filter
open QuantumTheory.Transport
open scoped Interval

/-- Real-valued closed form of the normalized radial `σₓ` current-rung integrand. -/
def continuumBornRetardedAdvancedPauliXCurrentRungRadialXIntegrandReal
    (v m p probeEnergy disorderStrength hbar : ℝ) : ℝ :=
  continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar *
    2 * Real.pi * p *
    (1 + continuumBornDampingScale v disorderStrength hbar ^ 2) *
    (probeEnergy ^ 2 - m ^ 2) *
    (continuumBornRADenominatorProduct
      v m p probeEnergy disorderStrength hbar)⁻¹

/-- The real current-rung kernel embeds exactly into the existing complex-valued radial API. -/
theorem coe_continuumBornRetardedAdvancedPauliXCurrentRungRadialXIntegrandReal
    (v m p probeEnergy disorderStrength hbar : ℝ) :
    (continuumBornRetardedAdvancedPauliXCurrentRungRadialXIntegrandReal
        v m p probeEnergy disorderStrength hbar : ℂ) =
      continuumBornRetardedAdvancedPauliXCurrentRungRadialXIntegrand
        v m p probeEnergy disorderStrength hbar := by
  rw [continuumBornRetardedAdvancedPauliXCurrentRungRadialXIntegrand_eq_closed]
  unfold continuumBornRetardedAdvancedPauliXCurrentRungRadialXIntegrandReal
  push_cast
  ring

/-- Finite-cutoff real `σₓ` coefficient of the fully normalized Born RA current rung. -/
noncomputable def finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungXCoefficient
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℝ :=
  ∫ p in (0 : ℝ)..pMax,
    continuumBornRetardedAdvancedPauliXCurrentRungRadialXIntegrandReal
      v m p probeEnergy disorderStrength hbar

/-- The real normalized finite-cutoff `σₓ` current-rung coefficient is exactly the finite-cutoff
Green-product coefficient multiplied by the physical current-rung prefactor. -/
theorem coe_finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungXCoefficient_eq_prefactor_mul_greenProduct
    (v m probeEnergy disorderStrength hbar pMax : ℝ) :
    (finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungXCoefficient
        v m probeEnergy disorderStrength hbar pMax : ℂ) =
      (continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar : ℂ) *
        finiteCutoffContinuumBornRetardedAdvancedPauliXRadialXCoefficient
          v m probeEnergy disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungXCoefficient
  rw [← Complex.ofRealLI_apply
    (∫ p in (0 : ℝ)..pMax,
      continuumBornRetardedAdvancedPauliXCurrentRungRadialXIntegrandReal
        v m p probeEnergy disorderStrength hbar)]
  rw [← Complex.ofRealLI.intervalIntegral_comp_comm]
  rw [show
      (fun p : ℝ => Complex.ofRealLI
        (continuumBornRetardedAdvancedPauliXCurrentRungRadialXIntegrandReal
          v m p probeEnergy disorderStrength hbar)) =
      (fun p : ℝ =>
        (continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar : ℂ) *
          continuumBornRetardedAdvancedPauliXRadialXIntegrand
            v m p probeEnergy disorderStrength hbar) by
    funext p
    rw [Complex.ofRealLI_apply,
      coe_continuumBornRetardedAdvancedPauliXCurrentRungRadialXIntegrandReal]
    rfl]
  rw [intervalIntegral.integral_const_mul]
  rfl

/-- A zero radial cutoff gives a vanishing normalized longitudinal Born current-rung coefficient. -/
@[simp] theorem finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungXCoefficient_zero
    (v m probeEnergy disorderStrength hbar : ℝ) :
    finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungXCoefficient
      v m probeEnergy disorderStrength hbar 0 = 0 := by
  simp [finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungXCoefficient]

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

/-- Exact finite-cutoff arctangent evaluation of the fully normalized Born RA `σₓ` current rung.
The assumptions only keep the resonance width and radial velocity scale nonzero; no weak-disorder
limit is taken in this theorem. -/
theorem finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungXCoefficient_eq_arctan
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hv : v ≠ 0)
    (hwidth : continuumBornRADenominatorWidth
      v m probeEnergy disorderStrength hbar ≠ 0) :
    finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungXCoefficient
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
  unfold finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungXCoefficient
    continuumBornRetardedAdvancedPauliXCurrentRungRadialXIntegrandReal
  rw [show
      (fun p : ℝ =>
        continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar *
          2 * Real.pi * p *
          (1 + continuumBornDampingScale v disorderStrength hbar ^ 2) *
          (probeEnergy ^ 2 - m ^ 2) *
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
  ring

/-- Exact endpoint formula with the disorder normalization already cancelled against the resonance
width.  This is the form adapted to the `disorderStrength → 0⁺` limit. -/
theorem finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungXCoefficient_eq_arctan_normalized
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hv : v ≠ 0) (hhbar : hbar ≠ 0) (hdisorder : disorderStrength ≠ 0)
    (hsum : probeEnergy ^ 2 + m ^ 2 ≠ 0) :
    finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungXCoefficient
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
  rw [finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungXCoefficient_eq_arctan
    v m probeEnergy disorderStrength hbar pMax hv hwidth]
  rw [continuumBornRetardedAdvancedCurrentRungPrefactor_eq_dampingScale
    v disorderStrength hbar hv hhbar]
  unfold continuumBornRADenominatorWidth
  field_simp [hv, hhbar, hgamma, hsum, Real.pi_ne_zero]

/-- The weak-disorder metallic target coefficient before solving the ladder equation. -/
def continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
    (m probeEnergy : ℝ) : ℝ :=
  (probeEnergy ^ 2 - m ^ 2) / (2 * (probeEnergy ^ 2 + m ^ 2))

/-- The scalar ladder denominator generated by the weak-disorder current-rung coefficient has the
same massive-Dirac angular factor that appears in the microscopic transport lifetime. -/
theorem one_sub_continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
    (m probeEnergy : ℝ) (hsum : probeEnergy ^ 2 + m ^ 2 ≠ 0) :
    1 - continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
        m probeEnergy =
      (probeEnergy ^ 2 + 3 * m ^ 2) /
        (2 * (probeEnergy ^ 2 + m ^ 2)) := by
  unfold continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
  field_simp [hsum]
  ring

/-- Solving the scalar ladder equation gives the transport-over-single-particle lifetime factor. -/
theorem inv_one_sub_continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
    (m probeEnergy : ℝ)
    (hden : probeEnergy ^ 2 + 3 * m ^ 2 ≠ 0) :
    (1 - continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
        m probeEnergy)⁻¹ =
      2 * (probeEnergy ^ 2 + m ^ 2) /
        (probeEnergy ^ 2 + 3 * m ^ 2) := by
  have hsum : probeEnergy ^ 2 + m ^ 2 ≠ 0 := by
    intro hzero
    have hE : probeEnergy = 0 := by
      nlinarith [sq_nonneg probeEnergy, sq_nonneg m]
    have hm : m = 0 := by
      nlinarith [sq_nonneg probeEnergy, sq_nonneg m]
    exact hden (by simp [hE, hm])
  rw [one_sub_continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
    m probeEnergy hsum]
  field_simp [hden, hsum]

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

The cutoff condition `probeEnergy² - m² < v² pMax²` is exactly what forces the two arctangent
endpoints to lie on opposite sides of the resonance as the disorder broadening vanishes. -/
theorem tendsto_finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungXCoefficient_disorder_zero
    (v m probeEnergy hbar pMax : ℝ)
    (hv : v ≠ 0) (hhbar : 0 < hbar) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun disorderStrength : ℝ =>
        finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungXCoefficient
          v m probeEnergy disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
          m probeEnergy)) := by
  have hprobe : 0 < probeEnergy := lt_of_le_of_lt (abs_nonneg m) hmetal
  have hdelta : 0 < probeEnergy ^ 2 - m ^ 2 := by
    rw [← sq_abs m]
    nlinarith [abs_nonneg m]
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
