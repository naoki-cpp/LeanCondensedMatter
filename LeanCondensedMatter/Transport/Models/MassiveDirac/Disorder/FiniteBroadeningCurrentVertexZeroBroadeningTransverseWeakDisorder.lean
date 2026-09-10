import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertexZeroBroadeningWeakDisorder
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Scaled transverse weak-disorder limit of the zero-broadening current rung

The raw transverse component of the fixed-cutoff zero-broadening source-`.x` Born-Dyson current rung
vanishes as `W → 0⁺`. The ordered Hall response consumes the first nonvanishing coefficient instead,
so this module keeps the quotient by the positive disorder strength before taking that limit.

The proof reuses the already-established full rung-vector weak-disorder limit and the fact that the
longitudinal and transverse integrated rung entries share the same radial kernel. No conductivity,
ultraviolet, thermodynamic, or simultaneous broadening/disorder limit is introduced here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter MeasureTheory QuantumTheory.Transport
open scoped Interval

private theorem denominatorBoundaryValue_retarded_sub_advanced
    (v m probeEnergy pMax : ℝ) (hvelocity : v ≠ 0) :
    finiteCutoffContinuumBornDenominatorIntegralBoundaryValue
        .retarded v m probeEnergy pMax -
      finiteCutoffContinuumBornDenominatorIntegralBoundaryValue
        .advanced v m probeEnergy pMax =
      -Complex.I * (((Real.pi / v ^ 2 : ℝ) : ℂ)) := by
  have hnegIMul (r : ℝ) :
      -Complex.I * (r : ℂ) = (⟨0, -r⟩ : ℂ) := by
    apply Complex.ext <;> simp
  rw [hnegIMul]
  apply Complex.ext
  · simp [finiteCutoffContinuumBornDenominatorIntegralBoundaryValue,
      pauliGreenDenominator, pauliGreenDenominatorOfRegulator, energySq,
      spectralParameterOfRegulator, SpectralSide.regulator]
  · simp [finiteCutoffContinuumBornDenominatorIntegralBoundaryValue]
    field_simp [hvelocity]
    norm_num

private theorem transverseAngularNumeratorBoundary_eq_disorder_mul
    (v m probeEnergy disorderStrength hbar pMax : ℝ) (hvelocity : v ≠ 0) :
    finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumeratorZeroBroadeningBoundary
        .y .x v m probeEnergy disorderStrength hbar pMax =
      (disorderStrength : ℂ) *
        (((2 * Real.pi * continuumBornAngularMeasurePrefactor hbar * probeEnergy * m /
          v ^ 2 : ℝ) : ℂ)) := by
  let a : ℂ := ((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ)
  let jR := finiteCutoffContinuumBornDenominatorIntegralBoundaryValue
    .retarded v m probeEnergy pMax
  let jA := finiteCutoffContinuumBornDenominatorIntegralBoundaryValue
    .advanced v m probeEnergy pMax
  have hj : jR - jA = -Complex.I * (((Real.pi / v ^ 2 : ℝ) : ℂ)) := by
    simpa [jR, jA] using
      denominatorBoundaryValue_retarded_sub_advanced v m probeEnergy pMax hvelocity
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumeratorZeroBroadeningBoundary
  simp only [inPlaneRotationMatrix_apply_y_x, inPlaneCoefficientVector]
  unfold finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary
    finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary
  change Complex.I *
      (((probeEnergy : ℂ) - a * ((probeEnergy : ℂ) * jA)) *
          ((m : ℂ) + a * ((m : ℂ) * jR)) -
        ((probeEnergy : ℂ) - a * ((probeEnergy : ℂ) * jR)) *
          ((m : ℂ) + a * ((m : ℂ) * jA))) = _
  rw [show Complex.I *
      (((probeEnergy : ℂ) - a * ((probeEnergy : ℂ) * jA)) *
          ((m : ℂ) + a * ((m : ℂ) * jR)) -
        ((probeEnergy : ℂ) - a * ((probeEnergy : ℂ) * jR)) *
          ((m : ℂ) + a * ((m : ℂ) * jA))) =
      2 * Complex.I * a * (probeEnergy : ℂ) * (m : ℂ) * (jR - jA) by ring]
  rw [hj]
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    rw [pow_two, Complex.I_mul_I]
  dsimp [a]
  push_cast
  field_simp [hvelocity]
  rw [hI]
  ring

private theorem currentRungBoundary_yx_mul_xxNumerator_eq_xx_mul_yxNumerator
    (v m probeEnergy disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary
        v m probeEnergy disorderStrength hbar pMax .y *
      finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumeratorZeroBroadeningBoundary
        .x .x v m probeEnergy disorderStrength hbar pMax =
    finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary
        v m probeEnergy disorderStrength hbar pMax .x *
      finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumeratorZeroBroadeningBoundary
        .y .x v m probeEnergy disorderStrength hbar pMax := by
  let common : ℝ → ℂ := fun p =>
    (((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ)) * (p : ℂ) *
      (((2 * Real.pi : ℝ) : ℂ)) *
      (finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary
        v m p probeEnergy disorderStrength hbar pMax)⁻¹
  let x := finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumeratorZeroBroadeningBoundary
    .x .x v m probeEnergy disorderStrength hbar pMax
  let y := finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumeratorZeroBroadeningBoundary
    .y .x v m probeEnergy disorderStrength hbar pMax
  have hx :
      finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary
          v m probeEnergy disorderStrength hbar pMax .x =
        x * ∫ p in (0 : ℝ)..pMax, common p := by
    unfold finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary
      finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficientZeroBroadeningBoundary
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro p _
    unfold finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrandZeroBroadeningBoundary
    dsimp [common, x]
    ring
  have hy :
      finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary
          v m probeEnergy disorderStrength hbar pMax .y =
        y * ∫ p in (0 : ℝ)..pMax, common p := by
    unfold finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary
      finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficientZeroBroadeningBoundary
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro p _
    unfold finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrandZeroBroadeningBoundary
    dsimp [common, y]
    ring
  rw [hx, hy]
  dsimp [x, y]
  ring

/-- At fixed cutoff beyond the metallic shell, the transverse zero-broadening current-rung
coefficient divided by `W` has a finite one-sided weak-disorder limit. -/
theorem tendsto_finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary_y_div_disorder_zero
    (v m probeEnergy hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun disorderStrength : ℝ =>
        finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary
            v m probeEnergy disorderStrength hbar pMax .y /
          (disorderStrength : ℂ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (((Real.pi * continuumBornAngularMeasurePrefactor hbar * probeEnergy * m /
          (v ^ 2 * (probeEnergy ^ 2 + m ^ 2)) : ℝ) : ℂ))) := by
  let l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  let x := fun disorderStrength : ℝ =>
    finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumeratorZeroBroadeningBoundary
      .x .x v m probeEnergy disorderStrength hbar pMax
  let rx := fun disorderStrength : ℝ =>
    finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary
      v m probeEnergy disorderStrength hbar pMax .x
  let ry := fun disorderStrength : ℝ =>
    finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary
      v m probeEnergy disorderStrength hbar pMax .y
  let c : ℂ := (((2 * Real.pi * continuumBornAngularMeasurePrefactor hbar * probeEnergy * m /
    v ^ 2 : ℝ) : ℂ))
  have hl : l ≤ nhds 0 := by
    dsimp [l, nhdsWithin]
    exact inf_le_left
  have hprobe : 0 < probeEnergy := lt_of_le_of_lt (abs_nonneg m) hmetal
  have hgap : 0 < probeEnergy ^ 2 - m ^ 2 := by
    rw [← sq_abs m]
    nlinarith [abs_nonneg m]
  have hsum : 0 < probeEnergy ^ 2 + m ^ 2 := by
    nlinarith [sq_pos_of_ne_zero (ne_of_gt hprobe), sq_nonneg m]
  have hvC : (v : ℂ) ≠ 0 := by
    exact_mod_cast hvelocity
  have hgapC : (probeEnergy : ℂ) ^ 2 - (m : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast ne_of_gt hgap
  have hsumC : (probeEnergy : ℂ) ^ 2 + (m : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast ne_of_gt hsum
  have hquarticC : (probeEnergy : ℂ) ^ 4 - (m : ℂ) ^ 4 ≠ 0 := by
    rw [show (probeEnergy : ℂ) ^ 4 - (m : ℂ) ^ 4 =
      ((probeEnergy : ℂ) ^ 2 - (m : ℂ) ^ 2) *
        ((probeEnergy : ℂ) ^ 2 + (m : ℂ) ^ 2) by ring]
    exact mul_ne_zero hgapC hsumC
  have hrung :=
    tendsto_finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary_disorder_zero
      v m probeEnergy hbar pMax hvelocity hhbar hmetal hcutoff
  have hrx : Tendsto rx l
      (nhds (continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
        m probeEnergy : ℂ)) := by
    simpa [rx, l, inPlaneCoefficientVector] using tendsto_pi_nhds.mp hrung .x
  have hx : Tendsto x l (nhds (((probeEnergy ^ 2 - m ^ 2 : ℝ) : ℂ))) := by
    have hcont : ContinuousAt x 0 := by
      dsimp [x]
      unfold finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumeratorZeroBroadeningBoundary
      simp only [inPlaneRotationMatrix_apply_x_x, inPlaneCoefficientVector]
      unfold finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary
        finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary
      fun_prop
    convert hcont.tendsto.mono_left hl using 1
    simp [x, finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumeratorZeroBroadeningBoundary,
      finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary,
      finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary,
      inPlaneRotationMatrix, inPlaneCoefficientVector]
    ring
  have hx0 : (((probeEnergy ^ 2 - m ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast ne_of_gt hgap
  have hxNe : ∀ᶠ disorderStrength : ℝ in l, x disorderStrength ≠ 0 :=
    hx.eventually_ne hx0
  have hclosed := (hrx.mul (hx.inv₀ hx0)).const_mul c
  have htarget :
      c *
          ((continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
              m probeEnergy : ℂ) * (((probeEnergy ^ 2 - m ^ 2 : ℝ) : ℂ))⁻¹) =
        (((Real.pi * continuumBornAngularMeasurePrefactor hbar * probeEnergy * m /
          (v ^ 2 * (probeEnergy ^ 2 + m ^ 2)) : ℝ) : ℂ)) := by
    dsimp [c]
    unfold continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
    push_cast
    field_simp [hvC, hgapC, hsumC, hquarticC]
  rw [htarget] at hclosed
  apply Tendsto.congr' ?_ hclosed
  filter_upwards [self_mem_nhdsWithin, hxNe] with disorderStrength hdisorder hxNonzero
  have hdisorderC : (disorderStrength : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hdisorder
  have hcross :=
    currentRungBoundary_yx_mul_xxNumerator_eq_xx_mul_yxNumerator
      v m probeEnergy disorderStrength hbar pMax
  have hy := transverseAngularNumeratorBoundary_eq_disorder_mul
    v m probeEnergy disorderStrength hbar pMax hvelocity
  rw [hy] at hcross
  have hcross' :
      ry disorderStrength * x disorderStrength =
        rx disorderStrength * ((disorderStrength : ℂ) * c) := by
    simpa [rx, ry, x, c] using hcross
  symm
  calc
    ry disorderStrength / (disorderStrength : ℂ) =
        (ry disorderStrength * x disorderStrength) /
          ((disorderStrength : ℂ) * x disorderStrength) := by
      field_simp [hdisorderC, hxNonzero]
    _ = (rx disorderStrength * ((disorderStrength : ℂ) * c)) /
          ((disorderStrength : ℂ) * x disorderStrength) := by
      rw [hcross']
    _ = c * (rx disorderStrength * (x disorderStrength)⁻¹) := by
      field_simp [hdisorderC, hxNonzero]

end

end QuantumTheory.Transport.Models.MassiveDirac
