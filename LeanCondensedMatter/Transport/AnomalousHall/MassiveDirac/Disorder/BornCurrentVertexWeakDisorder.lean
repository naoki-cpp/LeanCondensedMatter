import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.BornCurrentVertexFiniteCutoff
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Weak-disorder longitudinal Born current rung

This module starts from the finite-cutoff Born-dressed `Gᴿ σₓ Gᴬ` radial kernel and attaches the
external scalar-disorder line and physical momentum measure before taking any weak-disorder limit.
The unnormalized Green-product coefficient has the expected `1/γ` resonance, while the normalized
current-rung coefficient remains finite because the disorder-line prefactor contributes one power of
`γ`.

At nonzero Born damping the normalized `σₓ` coefficient is evaluated exactly as an arctangent
endpoint difference.  The weak-disorder limit and its connection to the microscopic transport
lifetime are proved downstream in `BornCurrentVertexTransportBridge.lean`; no Kubo conductivity or
clean finite-DC claim is made here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open MeasureTheory
open Filter
open QuantumTheory.Transport
open scoped Interval

/-- Real-valued closed form of the normalized radial `σₓ` current-rung integrand.  This is the
physical current-rung normalization from `BornCurrentVertexRadial`, not the unnormalized Green
product. -/
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

private theorem continuumBornRADenominatorProduct_ne_zero_of_width_ne_zero
    (v m p probeEnergy disorderStrength hbar : ℝ)
    (hwidth : continuumBornRADenominatorWidth
      v m probeEnergy disorderStrength hbar ≠ 0) :
    continuumBornRADenominatorProduct
      v m p probeEnergy disorderStrength hbar ≠ 0 := by
  unfold continuumBornRADenominatorProduct
  have hwidthSq :
      0 < continuumBornRADenominatorWidth
        v m probeEnergy disorderStrength hbar ^ 2 := sq_pos_of_ne_zero hwidth
  nlinarith [sq_nonneg
    (continuumBornRADenominatorCenter v m p probeEnergy disorderStrength hbar)]

private theorem hasDerivAt_continuumBornRADenominatorCenter
    (v m probeEnergy disorderStrength hbar p : ℝ) :
    HasDerivAt
      (fun q : ℝ => continuumBornRADenominatorCenter
        v m q probeEnergy disorderStrength hbar)
      (-2 * v ^ 2 * p) p := by
  unfold continuumBornRADenominatorCenter
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    (((hasDerivAt_id p).pow 2).const_mul (v ^ 2)).const_sub
      ((probeEnergy ^ 2 - m ^ 2) *
        (1 - continuumBornDampingScale v disorderStrength hbar ^ 2))

private theorem hasDerivAt_continuumBornRetardedAdvancedCurrentRungArctanPhase
    (v m probeEnergy disorderStrength hbar p : ℝ)
    (hwidth : continuumBornRADenominatorWidth
      v m probeEnergy disorderStrength hbar ≠ 0) :
    HasDerivAt
      (fun q : ℝ => continuumBornRetardedAdvancedCurrentRungArctanPhase
        v m q probeEnergy disorderStrength hbar)
      (-2 * v ^ 2 * p *
          continuumBornRADenominatorWidth v m probeEnergy disorderStrength hbar /
        continuumBornRADenominatorProduct
          v m p probeEnergy disorderStrength hbar) p := by
  have hratio :=
    (hasDerivAt_continuumBornRADenominatorCenter
      v m probeEnergy disorderStrength hbar p).div_const
        (continuumBornRADenominatorWidth v m probeEnergy disorderStrength hbar)
  have hatan := hratio.arctan
  unfold continuumBornRetardedAdvancedCurrentRungArctanPhase
  convert hatan using 1
  unfold continuumBornRADenominatorProduct
  field_simp [hwidth]
  ring

private theorem continuous_continuumBornRetardedAdvancedPauliXCurrentRungRadialXIntegrandReal
    (v m probeEnergy disorderStrength hbar : ℝ)
    (hwidth : continuumBornRADenominatorWidth
      v m probeEnergy disorderStrength hbar ≠ 0) :
    Continuous
      (continuumBornRetardedAdvancedPauliXCurrentRungRadialXIntegrandReal
        v m · probeEnergy disorderStrength hbar) := by
  have hden : Continuous (fun p : ℝ =>
      continuumBornRADenominatorProduct
        v m p probeEnergy disorderStrength hbar) := by
    unfold continuumBornRADenominatorProduct continuumBornRADenominatorCenter
    fun_prop
  have hinv : Continuous (fun p : ℝ =>
      (continuumBornRADenominatorProduct
        v m p probeEnergy disorderStrength hbar)⁻¹) :=
    hden.inv₀ (fun p =>
      continuumBornRADenominatorProduct_ne_zero_of_width_ne_zero
        v m p probeEnergy disorderStrength hbar hwidth)
  unfold continuumBornRetardedAdvancedPauliXCurrentRungRadialXIntegrandReal
  fun_prop

private theorem hasDerivAt_normalizedBornCurrentRungAntiderivative
    (v m probeEnergy disorderStrength hbar p : ℝ)
    (hv : v ≠ 0)
    (hwidth : continuumBornRADenominatorWidth
      v m probeEnergy disorderStrength hbar ≠ 0) :
    HasDerivAt
      (fun q : ℝ =>
        -(continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar *
            Real.pi *
            (1 + continuumBornDampingScale v disorderStrength hbar ^ 2) *
            (probeEnergy ^ 2 - m ^ 2) /
            (v ^ 2 * continuumBornRADenominatorWidth
              v m probeEnergy disorderStrength hbar)) *
          continuumBornRetardedAdvancedCurrentRungArctanPhase
            v m q probeEnergy disorderStrength hbar)
      (continuumBornRetardedAdvancedPauliXCurrentRungRadialXIntegrandReal
        v m p probeEnergy disorderStrength hbar) p := by
  let C : ℝ :=
    -(continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar *
        Real.pi *
        (1 + continuumBornDampingScale v disorderStrength hbar ^ 2) *
        (probeEnergy ^ 2 - m ^ 2) /
        (v ^ 2 * continuumBornRADenominatorWidth
          v m probeEnergy disorderStrength hbar))
  have hphase :=
    hasDerivAt_continuumBornRetardedAdvancedCurrentRungArctanPhase
      v m probeEnergy disorderStrength hbar p hwidth
  have hscaled := hphase.const_mul C
  have hproduct := continuumBornRADenominatorProduct_ne_zero_of_width_ne_zero
    v m p probeEnergy disorderStrength hbar hwidth
  have hderiv :
      C * (-2 * v ^ 2 * p *
          continuumBornRADenominatorWidth v m probeEnergy disorderStrength hbar /
        continuumBornRADenominatorProduct
          v m p probeEnergy disorderStrength hbar) =
        continuumBornRetardedAdvancedPauliXCurrentRungRadialXIntegrandReal
          v m p probeEnergy disorderStrength hbar := by
    dsimp [C]
    unfold continuumBornRetardedAdvancedPauliXCurrentRungRadialXIntegrandReal
    field_simp [hv, hwidth, hproduct, Real.pi_ne_zero]
  rw [hderiv] at hscaled
  simpa [C] using hscaled

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
  have hint : IntervalIntegrable
      (continuumBornRetardedAdvancedPauliXCurrentRungRadialXIntegrandReal
        v m · probeEnergy disorderStrength hbar) volume 0 pMax :=
    (continuous_continuumBornRetardedAdvancedPauliXCurrentRungRadialXIntegrandReal
      v m probeEnergy disorderStrength hbar hwidth).intervalIntegrable 0 pMax
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun p _ => hasDerivAt_normalizedBornCurrentRungAntiderivative
      v m probeEnergy disorderStrength hbar p hv hwidth) hint
  unfold finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungXCoefficient
  rw [hftc]
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

end

end AnomalousHall.MassiveDirac
