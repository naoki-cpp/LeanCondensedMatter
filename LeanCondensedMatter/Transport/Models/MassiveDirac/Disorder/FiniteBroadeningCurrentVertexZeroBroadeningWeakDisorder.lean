import LeanCondensedMatter.Analysis.Lorentzian.RadialQuadratic
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.BornCurrentVertexRung
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningLadderZeroBroadening
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Weak-disorder limit of the zero-broadening Born-Dyson current rung

The canonical fixed-cutoff zero-broadening source-`.x` rung is reduced privately to the shared
quadratic Lorentzian and then sent through the separate one-sided `W → 0⁺` limit. No exact radial
normal-form API, cutoff limit, or simultaneous broadening/disorder limit is exposed.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter MeasureTheory QuantumTheory.Transport
open scoped Interval

private def boundaryRACenter
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℝ :=
  (finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
    .retarded v m 0 probeEnergy disorderStrength hbar pMax).re

private def boundaryRAWidth
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℝ :=
  2 * continuumBornDampingScale v disorderStrength hbar *
    (probeEnergy ^ 2 + m ^ 2 -
      finiteCutoffContinuumBornBoundaryRealRenormalization
        v m probeEnergy disorderStrength hbar pMax * (probeEnergy ^ 2 - m ^ 2))

private theorem star_boundaryIntegral
    (side : SpectralSide) (v m probeEnergy pMax : ℝ) :
    star (finiteCutoffContinuumBornDenominatorIntegralBoundaryValue
      side v m probeEnergy pMax) =
      finiteCutoffContinuumBornDenominatorIntegralBoundaryValue
        side.opposite v m probeEnergy pMax := by
  cases side <;>
    apply Complex.ext <;>
    simp [finiteCutoffContinuumBornDenominatorIntegralBoundaryValue,
      pauliGreenDenominator, SpectralSide.regulator, SpectralSide.opposite]

private theorem star_boundaryDysonDenominator
    (side : SpectralSide)
    (v m p probeEnergy disorderStrength hbar pMax : ℝ) :
    star (finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
      side v m p probeEnergy disorderStrength hbar pMax) =
      finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
        side.opposite v m p probeEnergy disorderStrength hbar pMax := by
  simp [finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary,
    finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary,
    finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary, star_boundaryIntegral]

private theorem boundaryRetardedDenominator_im_eq_width
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0) :
    (finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
      .retarded v m 0 probeEnergy disorderStrength hbar pMax).im =
      boundaryRAWidth v m probeEnergy disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
    finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary
    finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary boundaryRAWidth
    finiteCutoffContinuumBornBoundaryRealRenormalization
  simp only [pow_two, Complex.sub_im, Complex.sub_re, Complex.add_im, Complex.add_re,
    Complex.mul_im, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, zero_mul,
    add_zero, zero_add, finiteCutoffContinuumBornDenominatorIntegralBoundaryValue_im,
    SpectralSide.sign_retarded]
  rw [continuumBornDampingScale_eq_selfEnergyPrefactor
    v disorderStrength hbar hvelocity hhbar]
  ring

private theorem boundaryRAProduct_eq
    (v m p probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary
        v m p probeEnergy disorderStrength hbar pMax =
      (((boundaryRACenter v m probeEnergy disorderStrength hbar pMax - v ^ 2 * p ^ 2) ^ 2 +
        boundaryRAWidth v m probeEnergy disorderStrength hbar pMax ^ 2 : ℝ) : ℂ) := by
  let D0 := finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
    .retarded v m 0 probeEnergy disorderStrength hbar pMax
  let D := finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
    .retarded v m p probeEnergy disorderStrength hbar pMax
  have hradial : D = D0 - ((v ^ 2 * p ^ 2 : ℝ) : ℂ) := by
    dsimp [D, D0]
    unfold finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
    push_cast
    ring
  have hD0im : D0.im = boundaryRAWidth
      v m probeEnergy disorderStrength hbar pMax := by
    dsimp [D0]
    exact boundaryRetardedDenominator_im_eq_width
      v m probeEnergy disorderStrength hbar pMax hvelocity hhbar
  have hstar : star D = finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
      .advanced v m p probeEnergy disorderStrength hbar pMax := by
    dsimp [D]
    simpa [SpectralSide.opposite] using
      (star_boundaryDysonDenominator
        .retarded v m p probeEnergy disorderStrength hbar pMax)
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary
  change D * _ = _
  rw [← hstar]
  rw [show D * star D = (Complex.normSq D : ℂ) by simpa using Complex.mul_conj D,
    hradial, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    sub_zero, hD0im]
  dsimp [D0, boundaryRACenter]
  push_cast
  ring

private theorem currentRungBoundary_eq_lorentzianIntegral
    (output : Direction2)
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0) :
    finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficientZeroBroadeningBoundary
        output .x v m probeEnergy disorderStrength hbar pMax =
      finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumeratorZeroBroadeningBoundary
          output .x v m probeEnergy disorderStrength hbar pMax *
        (((2 * Real.pi * (disorderStrength * momentumMeasurePrefactor hbar)) *
          (∫ p in (0 : ℝ)..pMax,
            p / ((boundaryRACenter v m probeEnergy disorderStrength hbar pMax - v ^ 2 * p ^ 2) ^ 2 +
              boundaryRAWidth v m probeEnergy disorderStrength hbar pMax ^ 2)) : ℝ) : ℂ) := by
  let A := boundaryRACenter v m probeEnergy disorderStrength hbar pMax
  let B := boundaryRAWidth v m probeEnergy disorderStrength hbar pMax
  let N := finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumeratorZeroBroadeningBoundary
    output .x v m probeEnergy disorderStrength hbar pMax
  let scale := 2 * Real.pi * (disorderStrength * momentumMeasurePrefactor hbar)
  have hintegrand (p : ℝ) :
      finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrandZeroBroadeningBoundary
          output .x v m p probeEnergy disorderStrength hbar pMax =
        N * (((scale * (p / ((A - v ^ 2 * p ^ 2) ^ 2 + B ^ 2)) : ℝ)) : ℂ) := by
    unfold finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrandZeroBroadeningBoundary
    rw [boundaryRAProduct_eq v m p probeEnergy disorderStrength hbar pMax hvelocity hhbar]
    dsimp [A, B, N, scale]
    push_cast
    simp [div_eq_mul_inv]
    ring
  have hcast :
      (∫ p in (0 : ℝ)..pMax,
        (((scale * (p / ((A - v ^ 2 * p ^ 2) ^ 2 + B ^ 2)) : ℝ)) : ℂ)) =
        Complex.ofReal
          (∫ p in (0 : ℝ)..pMax,
            scale * (p / ((A - v ^ 2 * p ^ 2) ^ 2 + B ^ 2))) := by
    exact RCLike.intervalIntegral_ofReal (𝕜 := ℂ) (μ := volume)
      (f := fun p : ℝ => scale * (p / ((A - v ^ 2 * p ^ 2) ^ 2 + B ^ 2)))
      (a := 0) (b := pMax)
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficientZeroBroadeningBoundary
  simp_rw [hintegrand]
  rw [intervalIntegral.integral_const_mul, hcast, intervalIntegral.integral_const_mul]

/-- At fixed cutoff beyond the metallic shell, the canonical zero-broadening source-`.x` rung tends
as one in-plane vector to `(κ, 0)`. -/
theorem tendsto_finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary_disorder_zero
    (v m probeEnergy hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun disorderStrength =>
        finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary
          v m probeEnergy disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (inPlaneCoefficientVector
          (continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
            m probeEnergy : ℂ) 0)) := by
  let l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  let Q := fun disorderStrength : ℝ =>
    probeEnergy ^ 2 + m ^ 2 -
      finiteCutoffContinuumBornBoundaryRealRenormalization
        v m probeEnergy disorderStrength hbar pMax * (probeEnergy ^ 2 - m ^ 2)
  let center := fun disorderStrength : ℝ =>
    boundaryRACenter v m probeEnergy disorderStrength hbar pMax
  let width := fun disorderStrength : ℝ =>
    boundaryRAWidth v m probeEnergy disorderStrength hbar pMax
  let scale := fun disorderStrength : ℝ =>
    2 * Real.pi * (disorderStrength * momentumMeasurePrefactor hbar)
  have hl : l ≤ nhds 0 := by
    dsimp [l, nhdsWithin]
    exact inf_le_left
  have hprobe : 0 < probeEnergy := lt_of_le_of_lt (abs_nonneg m) hmetal
  have hgap : 0 < probeEnergy ^ 2 - m ^ 2 := by
    rw [← sq_abs m]
    nlinarith [abs_nonneg m]
  have hsum : 0 < probeEnergy ^ 2 + m ^ 2 := by
    nlinarith [sq_pos_of_ne_zero (ne_of_gt hprobe), sq_nonneg m]
  have hQ : Tendsto Q l (nhds (probeEnergy ^ 2 + m ^ 2)) := by
    have hcont : ContinuousAt Q 0 := by
      dsimp [Q]
      unfold finiteCutoffContinuumBornBoundaryRealRenormalization
      fun_prop
    convert hcont.tendsto.mono_left hl using 1
    all_goals simp [Q, finiteCutoffContinuumBornBoundaryRealRenormalization]
  have hwidth0 : Tendsto width l (nhds 0) := by
    have hcont : ContinuousAt width 0 := by
      dsimp [width]
      unfold boundaryRAWidth finiteCutoffContinuumBornBoundaryRealRenormalization
        continuumBornDampingScale
      fun_prop
    convert hcont.tendsto.mono_left hl using 1
    all_goals simp [width, boundaryRAWidth, finiteCutoffContinuumBornBoundaryRealRenormalization,
      continuumBornDampingScale]
  have hwidthPos : ∀ᶠ disorderStrength : ℝ in l, 0 < width disorderStrength := by
    filter_upwards [self_mem_nhdsWithin,
      hQ.eventually (Ioi_mem_nhds hsum)] with disorderStrength hdisorder hQPos
    have hgammaPos : 0 < continuumBornDampingScale v disorderStrength hbar := by
      unfold continuumBornDampingScale
      exact div_pos hdisorder
        (mul_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero hhbar))
          (sq_pos_of_ne_zero hvelocity))
    simpa [width, Q, boundaryRAWidth] using
      mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hgammaPos) hQPos
  have hwidth : Tendsto width l (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hwidth0, hwidthPos⟩
  have hcenter0 : Tendsto center l (nhds (probeEnergy ^ 2 - m ^ 2)) := by
    have hcont : ContinuousAt center 0 := by
      dsimp [center]
      unfold boundaryRACenter finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
        finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary
        finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary
      fun_prop
    convert hcont.tendsto.mono_left hl using 1
    all_goals simp [center, boundaryRACenter,
      finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary,
      finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary,
      finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary,
      pow_two, Complex.mul_re]
  have hcenterMax :
      Tendsto (fun disorderStrength => center disorderStrength - v ^ 2 * pMax ^ 2) l
        (nhds (probeEnergy ^ 2 - m ^ 2 - v ^ 2 * pMax ^ 2)) :=
    hcenter0.sub tendsto_const_nhds
  have hdenNe : 2 * Real.pi * (probeEnergy ^ 2 + m ^ 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (ne_of_gt hsum)
  have hscaleClosed := (tendsto_const_nhds.mul hQ).inv₀ hdenNe
  have hscale :
      Tendsto (fun disorderStrength =>
        scale disorderStrength * (2 * v ^ 2 * width disorderStrength)⁻¹) l
        (nhds ((2 * Real.pi * (probeEnergy ^ 2 + m ^ 2))⁻¹)) := by
    apply Tendsto.congr' ?_ hscaleClosed
    filter_upwards [self_mem_nhdsWithin,
      hQ.eventually (Ioi_mem_nhds hsum)] with disorderStrength hdisorder hQPos
    have hgammaNe : continuumBornDampingScale v disorderStrength hbar ≠ 0 := by
      unfold continuumBornDampingScale
      exact div_ne_zero (ne_of_gt hdisorder)
        (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hhbar))
          (pow_ne_zero 2 hvelocity))
    have hpref := continuumBornRetardedAdvancedCurrentRungPrefactor_eq_dampingScale
      v disorderStrength hbar hvelocity hhbar
    dsimp [scale, width, Q]
    unfold boundaryRAWidth
    rw [show disorderStrength * momentumMeasurePrefactor hbar =
        continuumBornDampingScale v disorderStrength hbar * v ^ 2 / Real.pi ^ 2 by
      simpa [continuumBornRetardedAdvancedCurrentRungPrefactor] using hpref]
    field_simp [hvelocity, hgammaNe, ne_of_gt hQPos, Real.pi_ne_zero]
  have hkernel := tendsto_scaled_integral_radialQuadraticLorentzian_nhdsGT_zero
    v pMax hvelocity hcenter0 hgap hcenterMax (by linarith) hwidth hscale
  rw [tendsto_pi_nhds]
  intro output
  let n0 : ℂ := match output with
    | .x => (probeEnergy ^ 2 - m ^ 2 : ℝ)
    | .y => 0
  have hE (side : SpectralSide) :
      Tendsto
        (fun disorderStrength : ℝ =>
          finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary
            side v m probeEnergy disorderStrength hbar pMax)
        l (nhds (probeEnergy : ℂ)) := by
    have hcont : ContinuousAt
        (fun disorderStrength : ℝ =>
          finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary
            side v m probeEnergy disorderStrength hbar pMax) 0 := by
      unfold finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary
      fun_prop
    convert hcont.tendsto.mono_left hl using 1
    all_goals simp [finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary]
  have hM (side : SpectralSide) :
      Tendsto
        (fun disorderStrength : ℝ =>
          finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary
            side v m probeEnergy disorderStrength hbar pMax)
        l (nhds (m : ℂ)) := by
    have hcont : ContinuousAt
        (fun disorderStrength : ℝ =>
          finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary
            side v m probeEnergy disorderStrength hbar pMax) 0 := by
      unfold finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary
      fun_prop
    convert hcont.tendsto.mono_left hl using 1
    all_goals simp [finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary]
  have hX := (hE .retarded).mul (hE .advanced) |>.sub ((hM .retarded).mul (hM .advanced))
  have hY := (((hE .advanced).mul (hM .retarded)).sub
    ((hE .retarded).mul (hM .advanced))).const_mul Complex.I
  have hnum' :
      Tendsto
        (fun disorderStrength : ℝ =>
          finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumeratorZeroBroadeningBoundary
            output .x v m probeEnergy disorderStrength hbar pMax)
        l (nhds n0) := by
    cases output
    · simpa [n0,
        finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumeratorZeroBroadeningBoundary,
        inPlaneRotationMatrix, inPlaneCoefficientVector, pow_two] using hX
    · simpa [n0,
        finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumeratorZeroBroadeningBoundary,
        inPlaneRotationMatrix, inPlaneCoefficientVector, pow_two] using hY
  have hclosed := hnum'.mul hkernel.ofReal
  have htarget :
      n0 * ((((2 * Real.pi * (probeEnergy ^ 2 + m ^ 2))⁻¹ * Real.pi : ℝ) : ℂ)) =
        inPlaneCoefficientVector
          (continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
            m probeEnergy : ℂ) 0 output := by
    cases output
    · dsimp [n0]
      simp only [inPlaneCoefficientVector]
      unfold continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
      push_cast
      field_simp [Real.pi_ne_zero, ne_of_gt hsum]
    · simp [n0, inPlaneCoefficientVector]
  rw [htarget] at hclosed
  apply Tendsto.congr' ?_ hclosed
  filter_upwards with disorderStrength
  simpa [finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary,
    center, width, scale] using
    (currentRungBoundary_eq_lorentzianIntegral
      output v m probeEnergy disorderStrength hbar pMax hvelocity hhbar).symm

end

end QuantumTheory.Transport.Models.MassiveDirac
