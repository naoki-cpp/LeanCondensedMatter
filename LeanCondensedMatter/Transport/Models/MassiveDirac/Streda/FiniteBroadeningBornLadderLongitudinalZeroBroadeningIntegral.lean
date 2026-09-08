import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderRadialDenominator
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningLadderZeroBroadening
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningBornInvertibility
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Zero-broadening longitudinal Středa radial integral

The source-`.x` response is reduced to the integrated RA current rung plus elementary RR/AA endpoint
terms. This gives its fixed-disorder `η → 0⁺` boundary without a second Středa DCT layer.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter MeasureTheory QuantumTheory.Transport
open scoped Interval

private theorem intervalIntegrable_and_integral_radialQuadraticInverseSquare
    (v pMax : ℝ) (A : ℂ) (hvelocity : v ≠ 0)
    (hden : ∀ p : ℝ, A - (((v ^ 2 * p ^ 2 : ℝ) : ℂ)) ≠ 0) :
    IntervalIntegrable
        (fun p : ℝ => (p : ℂ) * A * (A - (((v ^ 2 * p ^ 2 : ℝ) : ℂ)))⁻¹ ^ 2)
        volume 0 pMax ∧
      (∫ p in (0 : ℝ)..pMax,
        (p : ℂ) * A * (A - (((v ^ 2 * p ^ 2 : ℝ) : ℂ)))⁻¹ ^ 2) =
        ((((2 * v ^ 2 : ℝ) : ℂ))⁻¹ * A) *
          ((A - (((v ^ 2 * pMax ^ 2 : ℝ) : ℂ)))⁻¹ - A⁻¹) := by
  let c : ℂ := ((v ^ 2 : ℝ) : ℂ)
  let g : ℂ → ℂ := fun z => A - c * z ^ 2
  let F : ℂ → ℂ := fun z => ((2 : ℂ) * c)⁻¹ * A * (g z)⁻¹
  have hvC : (v : ℂ) ≠ 0 := by exact_mod_cast hvelocity
  have hg : ∀ p : ℝ, HasDerivAt g (-2 * c * (p : ℂ)) (p : ℂ) := by
    intro p
    dsimp [g]
    convert! ((hasDerivAt_pow 2 (p : ℂ)).const_mul c).const_sub A using 1
    all_goals ring
  have hF : ∀ p : ℝ,
      HasDerivAt (fun x : ℝ => F (x : ℂ))
        ((p : ℂ) * A * (A - (((v ^ 2 * p ^ 2 : ℝ) : ℂ)))⁻¹ ^ 2) p := by
    intro p
    have hgp : g (p : ℂ) ≠ 0 := by simpa [g, c] using hden p
    have hreal := (((hg p).inv hgp).const_mul (((2 : ℂ) * c)⁻¹ * A)).comp_ofReal
    convert hreal using 1
    · rfl
    · dsimp [g, c] at hgp ⊢
      simp only [Complex.ofReal_mul, Complex.ofReal_pow]
      field_simp [hgp, hvC]
  have hinv : Continuous (fun p : ℝ =>
      (A - (((v ^ 2 * p ^ 2 : ℝ) : ℂ)))⁻¹) :=
    (show Continuous (fun p : ℝ => A - (((v ^ 2 * p ^ 2 : ℝ) : ℂ))) by fun_prop).inv₀ hden
  have hint : IntervalIntegrable
      (fun p : ℝ => (p : ℂ) * A * (A - (((v ^ 2 * p ^ 2 : ℝ) : ℂ)))⁻¹ ^ 2)
      volume 0 pMax := by
    apply Continuous.intervalIntegrable
    exact ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const).mul (hinv.pow 2)
  refine ⟨hint, ?_⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun p _ => hF p) hint]
  simp [F, g, c, sub_eq_add_neg, mul_assoc]
  ring

private def finiteBroadeningSameSideRadialEndpoint
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  ((((2 * v ^ 2 : ℝ) : ℂ))⁻¹ *
      (finiteCutoffContinuumBornEffectiveEnergy
          side v m probeEnergy broadening disorderStrength hbar pMax ^ 2 -
        finiteCutoffContinuumBornEffectiveMass
          side v m probeEnergy broadening disorderStrength hbar pMax ^ 2)) *
    ((finiteCutoffContinuumBornDysonDenominator
        side v m pMax 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ -
      (finiteCutoffContinuumBornDysonDenominator
        side v m 0 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹)

private def zeroBroadeningSameSideRadialEndpoint
    (side : SpectralSide)
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  ((((2 * v ^ 2 : ℝ) : ℂ))⁻¹ *
      (finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary
          side v m probeEnergy disorderStrength hbar pMax ^ 2 -
        finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary
          side v m probeEnergy disorderStrength hbar pMax ^ 2)) *
    ((finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
        side v m pMax probeEnergy disorderStrength hbar pMax)⁻¹ -
      (finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
        side v m 0 probeEnergy disorderStrength hbar pMax)⁻¹)

private def finiteBroadeningLongitudinalMomentumEndpointForm
    (e v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  let q : ℂ := (((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))
  let pref : ℂ := ((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ)
  let solved := finiteCutoffContinuumBornDysonLadderSolvedVector
    v m probeEnergy broadening disorderStrength hbar pMax
  let kx := finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient
    .x .x v m probeEnergy broadening disorderStrength hbar pMax
  let ky := finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient
    .y .x v m probeEnergy broadening disorderStrength hbar pMax
  2 * q ^ 2 * pref⁻¹ * inPlaneLadderAction kx ky solved .x -
    (((2 * Real.pi : ℝ) : ℂ)) * q ^ 2 *
      (finiteBroadeningSameSideRadialEndpoint
          .retarded v m probeEnergy broadening disorderStrength hbar pMax +
        finiteBroadeningSameSideRadialEndpoint
          .advanced v m probeEnergy broadening disorderStrength hbar pMax)

/-- Fixed-disorder zero-broadening boundary of the canonical longitudinal Středa momentum integral. -/
def finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceMomentumIntegralZeroBroadeningBoundary
    (e v m probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  let q : ℂ := (((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))
  let pref : ℂ := ((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ)
  let solved := finiteCutoffContinuumBornDysonLadderSolvedVectorZeroBroadeningBoundary
    v m probeEnergy disorderStrength hbar pMax
  let kx := finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficientZeroBroadeningBoundary
    .x .x v m probeEnergy disorderStrength hbar pMax
  let ky := finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficientZeroBroadeningBoundary
    .y .x v m probeEnergy disorderStrength hbar pMax
  2 * q ^ 2 * pref⁻¹ * inPlaneLadderAction kx ky solved .x -
    (((2 * Real.pi : ℝ) : ℂ)) * q ^ 2 *
      (zeroBroadeningSameSideRadialEndpoint
          .retarded v m probeEnergy disorderStrength hbar pMax +
        zeroBroadeningSameSideRadialEndpoint
          .advanced v m probeEnergy disorderStrength hbar pMax)

private theorem finiteBroadeningSameSide_integrable_and_integral_eq_endpoint
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hbroadening : broadening ≠ 0)
    (hdisorder : 0 ≤ disorderStrength) (hpMax : 0 ≤ pMax) :
    IntervalIntegrable
        (fun p : ℝ =>
          (p : ℂ) *
            (finiteCutoffContinuumBornDysonDenominator
              side v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ ^ 2 *
            (finiteCutoffContinuumBornEffectiveEnergy
                side v m probeEnergy broadening disorderStrength hbar pMax ^ 2 -
              finiteCutoffContinuumBornEffectiveMass
                side v m probeEnergy broadening disorderStrength hbar pMax ^ 2)) volume 0 pMax ∧
      (∫ p in (0 : ℝ)..pMax,
        (p : ℂ) *
          (finiteCutoffContinuumBornDysonDenominator
            side v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ ^ 2 *
          (finiteCutoffContinuumBornEffectiveEnergy
              side v m probeEnergy broadening disorderStrength hbar pMax ^ 2 -
            finiteCutoffContinuumBornEffectiveMass
              side v m probeEnergy broadening disorderStrength hbar pMax ^ 2)) =
        finiteBroadeningSameSideRadialEndpoint
          side v m probeEnergy broadening disorderStrength hbar pMax := by
  let A : ℂ :=
    finiteCutoffContinuumBornEffectiveEnergy
        side v m probeEnergy broadening disorderStrength hbar pMax ^ 2 -
      finiteCutoffContinuumBornEffectiveMass
        side v m probeEnergy broadening disorderStrength hbar pMax ^ 2
  have hden : ∀ p : ℝ, A - (((v ^ 2 * p ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    intro p
    simpa [A, finiteCutoffContinuumBornDysonDenominator] using
      (finiteCutoffContinuumBornDysonDenominator_ne_zero
        side v m p 0 probeEnergy broadening disorderStrength hbar pMax
        hbroadening hdisorder hpMax)
  simpa [A, finiteBroadeningSameSideRadialEndpoint,
    finiteCutoffContinuumBornDysonDenominator, mul_comm, mul_left_comm, mul_assoc] using
    (intervalIntegrable_and_integral_radialQuadraticInverseSquare
      v pMax A hvelocity hden)

private theorem finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral_x_eq_endpointForm
    (e v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hpMax : 0 ≤ pMax) (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 < disorderStrength) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral
        .x e v m probeEnergy broadening disorderStrength hbar pMax =
      finiteBroadeningLongitudinalMomentumEndpointForm
        e v m probeEnergy broadening disorderStrength hbar pMax := by
  let q : ℂ := (((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))
  let pref : ℂ := ((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ)
  let solved := finiteCutoffContinuumBornDysonLadderSolvedVector
    v m probeEnergy broadening disorderStrength hbar pMax
  let rx : ℝ → ℂ := fun p => finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand
    .x .x v m p probeEnergy broadening disorderStrength hbar pMax
  let ry : ℝ → ℂ := fun p => finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand
    .y .x v m p probeEnergy broadening disorderStrength hbar pMax
  let same : SpectralSide → ℝ → ℂ := fun side p =>
    (p : ℂ) * (finiteCutoffContinuumBornDysonDenominator
      side v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ ^ 2 *
      (finiteCutoffContinuumBornEffectiveEnergy
          side v m probeEnergy broadening disorderStrength hbar pMax ^ 2 -
        finiteCutoffContinuumBornEffectiveMass
          side v m probeEnergy broadening disorderStrength hbar pMax ^ 2)
  have hpref : pref ≠ 0 := by
    dsimp [pref, momentumMeasurePrefactor]
    exact_mod_cast mul_ne_zero (ne_of_gt hdisorder)
      (one_div_ne_zero (pow_ne_zero 2
        (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hhbar)))
  have hpointwise : ∀ p : ℝ,
      finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand
          .x e v m p probeEnergy broadening disorderStrength hbar pMax =
        2 * q ^ 2 * pref⁻¹ * (solved .x * rx p - solved .y * ry p) -
          (((2 * Real.pi : ℝ) : ℂ)) * q ^ 2 * (same .retarded p + same .advanced p) := by
    intro p
    have hdenR := finiteCutoffContinuumBornDysonDenominator_ne_zero
      .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
      hbroadening hdisorder.le hpMax
    have hdenA := finiteCutoffContinuumBornDysonDenominator_ne_zero
      .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
      hbroadening hdisorder.le hpMax
    rw [finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand_eq_radialCoefficient,
      finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient_x_eq_denominatorForm]
    dsimp [q, solved, rx, ry, same]
    rw [finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand,
      finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand,
      finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficient_eq_denominatorForm,
      finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficient_eq_denominatorForm]
    simp only [finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumerator,
      inPlaneRotationCoefficient, inPlaneRotationMatrix_apply_x_x,
      inPlaneRotationMatrix_apply_y_x]
    unfold finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
    rw [mul_inv_rev]
    push_cast
    field_simp [hpref, hdenR, hdenA] <;> ring_nf
  have hrx : IntervalIntegrable rx volume 0 pMax := by
    simpa [rx] using
      (continuous_finiteBroadeningBornCurrentRungRadialIntegrand
        .x .x v m probeEnergy broadening disorderStrength hbar pMax
        hbroadening hdisorder.le hpMax).intervalIntegrable (μ := volume) 0 pMax
  have hry : IntervalIntegrable ry volume 0 pMax := by
    simpa [ry] using
      (continuous_finiteBroadeningBornCurrentRungRadialIntegrand
        .y .x v m probeEnergy broadening disorderStrength hbar pMax
        hbroadening hdisorder.le hpMax).intervalIntegrable (μ := volume) 0 pMax
  obtain ⟨hrr, hrrEq⟩ := finiteBroadeningSameSide_integrable_and_integral_eq_endpoint
    .retarded v m probeEnergy broadening disorderStrength hbar pMax
    hvelocity hbroadening hdisorder.le hpMax
  obtain ⟨haa, haaEq⟩ := finiteBroadeningSameSide_integrable_and_integral_eq_endpoint
    .advanced v m probeEnergy broadening disorderStrength hbar pMax
    hvelocity hbroadening hdisorder.le hpMax
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral
  have hintegral :
      (∫ p in (0 : ℝ)..pMax,
        finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand
          .x e v m p probeEnergy broadening disorderStrength hbar pMax) =
      ∫ p in (0 : ℝ)..pMax,
        2 * q ^ 2 * pref⁻¹ * (solved .x * rx p - solved .y * ry p) -
          (((2 * Real.pi : ℝ) : ℂ)) * q ^ 2 * (same .retarded p + same .advanced p) := by
    apply intervalIntegral.integral_congr
    intro p _
    exact hpointwise p
  rw [hintegral]
  rw [intervalIntegral.integral_sub
    (((hrx.const_mul (solved .x)).sub (hry.const_mul (solved .y))).const_mul
      (2 * q ^ 2 * pref⁻¹))
    ((hrr.add haa).const_mul ((((2 * Real.pi : ℝ) : ℂ)) * q ^ 2))]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (hrx.const_mul (solved .x)) (hry.const_mul (solved .y)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_add hrr haa]
  rw [show (∫ p in (0 : ℝ)..pMax, same .retarded p) = finiteBroadeningSameSideRadialEndpoint
      .retarded v m probeEnergy broadening disorderStrength hbar pMax by simpa [same] using hrrEq]
  rw [show (∫ p in (0 : ℝ)..pMax, same .advanced p) = finiteBroadeningSameSideRadialEndpoint
      .advanced v m probeEnergy broadening disorderStrength hbar pMax by simpa [same] using haaEq]
  simp [finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient,
    finiteBroadeningLongitudinalMomentumEndpointForm, inPlaneLadderAction_apply_x,
    q, pref, solved, rx, ry]
  ring_nf

private theorem tendsto_finiteBroadeningSameSideRadialEndpoint_broadening_zero
    (side : SpectralSide)
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2)
    (hden0 : finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
      side v m 0 probeEnergy disorderStrength hbar pMax ≠ 0)
    (hdenMax : finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
      side v m pMax probeEnergy disorderStrength hbar pMax ≠ 0) :
    Tendsto
      (fun broadening : ℝ => finiteBroadeningSameSideRadialEndpoint
        side v m probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (zeroBroadeningSameSideRadialEndpoint
        side v m probeEnergy disorderStrength hbar pMax)) := by
  have hE := tendsto_finiteCutoffContinuumBornEffectiveEnergy_broadening_zero
    side v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hM := tendsto_finiteCutoffContinuumBornEffectiveMass_broadening_zero
    side v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hA := (hE.pow 2).sub (hM.pow 2)
  have hD0 := tendsto_finiteCutoffContinuumBornDysonDenominator_broadening_zero
    side v m 0 probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hDMax := tendsto_finiteCutoffContinuumBornDysonDenominator_broadening_zero
    side v m pMax probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hconst : Tendsto (fun _ : ℝ => ((((2 * v ^ 2 : ℝ) : ℂ))⁻¹))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((((2 * v ^ 2 : ℝ) : ℂ))⁻¹)) := tendsto_const_nhds
  simpa [finiteBroadeningSameSideRadialEndpoint, zeroBroadeningSameSideRadialEndpoint,
    finiteCutoffContinuumBornDysonDenominator,
    finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary, mul_assoc] using
    (hconst.mul hA).mul ((hDMax.inv₀ hdenMax).sub (hD0.inv₀ hden0))

/-- At fixed positive disorder and finite cutoff, the canonical longitudinal Středa momentum
integral converges directly to its zero-broadening boundary. -/
theorem tendsto_finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceMomentumIntegral_broadening_zero
    (e v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hpMax : 0 ≤ pMax) (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hdisorder : 0 < disorderStrength) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2)
    (hrenorm : finiteCutoffContinuumBornBoundaryRealRenormalization
      v m probeEnergy disorderStrength hbar pMax < 1)
    (hdet : finiteCutoffContinuumBornDysonLadderDeterminantZeroBroadeningBoundary
      v m probeEnergy disorderStrength hbar pMax ≠ 0) :
    Tendsto
      (fun broadening : ℝ => finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral
        .x e v m probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceMomentumIntegralZeroBroadeningBoundary
        e v m probeEnergy disorderStrength hbar pMax)) := by
  have hSolved :=
    tendsto_finiteCutoffContinuumBornDysonLadderSolvedVector_broadening_zero_of_boundary_realRenormalization_lt_one
      v m probeEnergy disorderStrength hbar pMax hpMax hvelocity hhbar
      hdisorder hmetal hcutoff hrenorm hdet
  have hAlpha := tendsto_pi_nhds.mp hSolved .x
  have hBeta := tendsto_pi_nhds.mp hSolved .y
  have hKx := tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient_broadening_zero_of_boundary_realRenormalization_lt_one
    .x .x v m probeEnergy disorderStrength hbar pMax hpMax hvelocity hhbar
    hdisorder hmetal hcutoff hrenorm
  have hKy := tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient_broadening_zero_of_boundary_realRenormalization_lt_one
    .y .x v m probeEnergy disorderStrength hbar pMax hpMax hvelocity hhbar
    hdisorder hmetal hcutoff hrenorm
  have hden (side : SpectralSide) (p : ℝ) :=
    finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary_ne_zero
      side v m p probeEnergy disorderStrength hbar pMax
      hvelocity hhbar hdisorder hmetal hrenorm
  have hRR := tendsto_finiteBroadeningSameSideRadialEndpoint_broadening_zero
    .retarded v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
    (hden .retarded 0) (hden .retarded pMax)
  have hAA := tendsto_finiteBroadeningSameSideRadialEndpoint_broadening_zero
    .advanced v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
    (hden .advanced 0) (hden .advanced pMax)
  have htotal :=
    (((hKx.mul hAlpha).sub (hKy.mul hBeta)).const_mul
      (2 * ((((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))) ^ 2 *
        (((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ))⁻¹)).sub
    ((hRR.add hAA).const_mul
      ((((2 * Real.pi : ℝ) : ℂ)) * ((((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))) ^ 2))
  have hEndpoint :
      Tendsto
        (fun broadening : ℝ =>
          finiteBroadeningLongitudinalMomentumEndpointForm
            e v m probeEnergy broadening disorderStrength hbar pMax)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceMomentumIntegralZeroBroadeningBoundary
            e v m probeEnergy disorderStrength hbar pMax)) := by
    simpa [finiteBroadeningLongitudinalMomentumEndpointForm,
      finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceMomentumIntegralZeroBroadeningBoundary,
      inPlaneLadderAction_apply_x] using htotal
  exact Tendsto.congr' (by
    filter_upwards [self_mem_nhdsWithin] with broadening hbroadening
    exact (finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral_x_eq_endpointForm
      e v m probeEnergy broadening disorderStrength hbar pMax hpMax hvelocity hhbar
      (ne_of_gt hbroadening) hdisorder).symm) hEndpoint

end

end QuantumTheory.Transport.Models.MassiveDirac
