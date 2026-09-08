import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderRadialDenominator
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningLadderZeroBroadening
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningBornInvertibility
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Zero-broadening longitudinal Středa radial integral

The longitudinal radial response splits into an RA part already supplied by the integrated current
rung and bare RR/AA same-side terms. The same-side radial integral is elementary: the quadratic
Dyson denominator turns it into an endpoint difference of inverse denominators. This avoids a second
radial dominated-convergence proof for the Středa response.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter MeasureTheory QuantumTheory.Transport
open scoped Interval

private def radialQuadraticInverseSquareEndpoint
    (v pMax : ℝ) (A : ℂ) : ℂ :=
  ((((2 * v ^ 2 : ℝ) : ℂ))⁻¹ * A) *
    ((A - (((v ^ 2 * pMax ^ 2 : ℝ) : ℂ)))⁻¹ - A⁻¹)

private theorem integral_radialQuadraticInverseSquare
    (v pMax : ℝ) (A : ℂ)
    (hvelocity : v ≠ 0)
    (hden : ∀ p : ℝ, A - (((v ^ 2 * p ^ 2 : ℝ) : ℂ)) ≠ 0) :
    (∫ p in (0 : ℝ)..pMax,
      (p : ℂ) * A * (A - (((v ^ 2 * p ^ 2 : ℝ) : ℂ)))⁻¹ ^ 2) =
      radialQuadraticInverseSquareEndpoint v pMax A := by
  let c : ℂ := ((v ^ 2 : ℝ) : ℂ)
  let g : ℂ → ℂ := fun z => A - c * z ^ 2
  let F : ℂ → ℂ := fun z => ((2 : ℂ) * c)⁻¹ * A * (g z)⁻¹
  have hc : c ≠ 0 := by
    simp [c, hvelocity]
  have hg : ∀ p : ℝ, HasDerivAt g (-2 * c * (p : ℂ)) (p : ℂ) := by
    intro p
    dsimp [g]
    convert! ((hasDerivAt_pow 2 (p : ℂ)).const_mul c).const_sub A using 1 <;> ring
  have hF : ∀ p : ℝ,
      HasDerivAt (fun x : ℝ => F (x : ℂ))
        ((p : ℂ) * A * (A - (((v ^ 2 * p ^ 2 : ℝ) : ℂ)))⁻¹ ^ 2) p := by
    intro p
    have hgp : g (p : ℂ) ≠ 0 := by
      simpa [g, c] using hden p
    have hcomplex := ((hg p).inv hgp).const_mul (((2 : ℂ) * c)⁻¹ * A)
    have hreal := hcomplex.comp_ofReal
    convert! hreal using 1
    · simp [F]
    · field_simp [hc, hgp]
      simp [g, c]
      ring
  have hcontinuous : Continuous (fun p : ℝ =>
      A - (((v ^ 2 * p ^ 2 : ℝ) : ℂ))) := by
    fun_prop
  have hinv : Continuous (fun p : ℝ =>
      (A - (((v ^ 2 * p ^ 2 : ℝ) : ℂ)))⁻¹) :=
    hcontinuous.inv₀ hden
  have hint : IntervalIntegrable
      (fun p : ℝ =>
        (p : ℂ) * A * (A - (((v ^ 2 * p ^ 2 : ℝ) : ℂ)))⁻¹ ^ 2)
      volume 0 pMax := by
    apply Continuous.intervalIntegrable
    exact ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const).mul (hinv.pow 2)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun p _ => hF p) hint
  simpa [F, g, c, radialQuadraticInverseSquareEndpoint, sub_eq_add_neg, mul_assoc] using hftc

private def finiteBroadeningSameSideRadialEndpoint
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  radialQuadraticInverseSquareEndpoint v pMax
    (finiteCutoffContinuumBornEffectiveEnergy
        side v m probeEnergy broadening disorderStrength hbar pMax ^ 2 -
      finiteCutoffContinuumBornEffectiveMass
        side v m probeEnergy broadening disorderStrength hbar pMax ^ 2)

private def zeroBroadeningSameSideRadialEndpoint
    (side : SpectralSide)
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  radialQuadraticInverseSquareEndpoint v pMax
    (finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary
        side v m probeEnergy disorderStrength hbar pMax ^ 2 -
      finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary
        side v m probeEnergy disorderStrength hbar pMax ^ 2)

private theorem integral_finiteBroadeningSameSide_eq_endpoint
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hbroadening : broadening ≠ 0)
    (hdisorder : 0 ≤ disorderStrength) (hpMax : 0 ≤ pMax) :
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
    (integral_radialQuadraticInverseSquare v pMax A hvelocity hden)

private theorem intervalIntegrable_finiteBroadeningCurrentRungRadialIntegrand
    (i j : Direction2)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    IntervalIntegrable
      (fun p =>
        finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand
          i j v m p probeEnergy broadening disorderStrength hbar pMax)
      volume 0 pMax := by
  have hdenContinuous : Continuous (fun p : ℝ =>
      finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
        v m p probeEnergy broadening disorderStrength hbar pMax) := by
    unfold finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
      finiteCutoffContinuumBornDysonDenominator
    fun_prop
  have hdenNe : ∀ p : ℝ,
      finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
        v m p probeEnergy broadening disorderStrength hbar pMax ≠ 0 := fun p =>
    finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct_ne_zero
      v m p probeEnergy broadening disorderStrength hbar pMax
      hbroadening hdisorder hpMax
  have hinv : Continuous (fun p : ℝ =>
      (finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
        v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹) :=
    hdenContinuous.inv₀ hdenNe
  have hfun :
      (fun p : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand
          i j v m p probeEnergy broadening disorderStrength hbar pMax) =
      (fun p : ℝ =>
        (((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ)) * (p : ℂ) *
          ((((2 * Real.pi : ℝ) : ℂ)) *
            (finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
              v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹ *
            finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumerator
              i j v m probeEnergy broadening disorderStrength hbar pMax)) := by
    funext p
    rw [finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand,
      finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficient_eq_denominatorForm]
  rw [hfun]
  apply Continuous.intervalIntegrable
  exact ((continuous_const.mul (Complex.continuous_ofReal.comp continuous_id)).mul
    ((continuous_const.mul hinv).mul continuous_const))

/-- Proof-independent finite-`η` longitudinal radial response after using the already integrated RA
current rung and evaluating the RR/AA same-side pieces by endpoints. -/
def finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceMomentumIntegralReduced
    (e v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  let q : ℂ := (((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))
  let pref : ℂ := ((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ)
  let alpha := finiteCutoffContinuumBornDysonLadderSolvedCoefficient
    .x v m probeEnergy broadening disorderStrength hbar pMax
  let beta := finiteCutoffContinuumBornDysonLadderSolvedCoefficient
    .y v m probeEnergy broadening disorderStrength hbar pMax
  let kx := finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient
    .x .x v m probeEnergy broadening disorderStrength hbar pMax
  let ky := finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient
    .y .x v m probeEnergy broadening disorderStrength hbar pMax
  2 * q ^ 2 * pref⁻¹ * (alpha * kx - beta * ky) -
    (((2 * Real.pi : ℝ) : ℂ)) * q ^ 2 *
      (finiteBroadeningSameSideRadialEndpoint
          .retarded v m probeEnergy broadening disorderStrength hbar pMax +
        finiteBroadeningSameSideRadialEndpoint
          .advanced v m probeEnergy broadening disorderStrength hbar pMax)

/-- Fixed-disorder zero-broadening boundary of the reduced longitudinal radial Středa response. -/
def finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceMomentumIntegralZeroBroadeningBoundary
    (e v m probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  let q : ℂ := (((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))
  let pref : ℂ := ((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ)
  let alpha := finiteCutoffContinuumBornDysonLadderSolvedCoefficientZeroBroadeningBoundary
    .x v m probeEnergy disorderStrength hbar pMax
  let beta := finiteCutoffContinuumBornDysonLadderSolvedCoefficientZeroBroadeningBoundary
    .y v m probeEnergy disorderStrength hbar pMax
  let kx := finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficientZeroBroadeningBoundary
    .x .x v m probeEnergy disorderStrength hbar pMax
  let ky := finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficientZeroBroadeningBoundary
    .y .x v m probeEnergy disorderStrength hbar pMax
  2 * q ^ 2 * pref⁻¹ * (alpha * kx - beta * ky) -
    (((2 * Real.pi : ℝ) : ℂ)) * q ^ 2 *
      (zeroBroadeningSameSideRadialEndpoint
          .retarded v m probeEnergy disorderStrength hbar pMax +
        zeroBroadeningSameSideRadialEndpoint
          .advanced v m probeEnergy disorderStrength hbar pMax)

/-- Whenever the finite-`η` ladder is regular, the physical source-`.x` Středa momentum integral is
exactly the reduced expression built from the integrated RA current rung and RR/AA endpoint terms. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral_x_eq_longitudinalReduced
    (e v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hpMax : 0 ≤ pMax) (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 < disorderStrength)
    (hdet : finiteCutoffContinuumBornDysonLadderRegular
      v m probeEnergy broadening disorderStrength hbar pMax) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral
        .x e v m probeEnergy broadening disorderStrength hbar pMax hdet =
      finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceMomentumIntegralReduced
        e v m probeEnergy broadening disorderStrength hbar pMax := by
  let q : ℂ := (((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))
  let pref : ℂ := ((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ)
  let alpha := finiteCutoffContinuumBornDysonLadderSolvedCoefficient
    .x v m probeEnergy broadening disorderStrength hbar pMax
  let beta := finiteCutoffContinuumBornDysonLadderSolvedCoefficient
    .y v m probeEnergy broadening disorderStrength hbar pMax
  let rx : ℝ → ℂ := fun p =>
    finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand
      .x .x v m p probeEnergy broadening disorderStrength hbar pMax
  let ry : ℝ → ℂ := fun p =>
    finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand
      .y .x v m p probeEnergy broadening disorderStrength hbar pMax
  let rr : ℝ → ℂ := fun p =>
    (p : ℂ) *
      (finiteCutoffContinuumBornDysonDenominator
        .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ ^ 2 *
      (finiteCutoffContinuumBornEffectiveEnergy
          .retarded v m probeEnergy broadening disorderStrength hbar pMax ^ 2 -
        finiteCutoffContinuumBornEffectiveMass
          .retarded v m probeEnergy broadening disorderStrength hbar pMax ^ 2)
  let aa : ℝ → ℂ := fun p =>
    (p : ℂ) *
      (finiteCutoffContinuumBornDysonDenominator
        .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ ^ 2 *
      (finiteCutoffContinuumBornEffectiveEnergy
          .advanced v m probeEnergy broadening disorderStrength hbar pMax ^ 2 -
        finiteCutoffContinuumBornEffectiveMass
          .advanced v m probeEnergy broadening disorderStrength hbar pMax ^ 2)
  have hpref : pref ≠ 0 := by
    dsimp [pref, momentumMeasurePrefactor]
    exact_mod_cast mul_ne_zero (ne_of_gt hdisorder)
      (one_div_ne_zero (pow_ne_zero 2
        (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hhbar)))
  have hpointwise : ∀ p : ℝ,
      finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand
          .x e v m p probeEnergy broadening disorderStrength hbar pMax hdet =
        2 * q ^ 2 * pref⁻¹ * (alpha * rx p - beta * ry p) -
          (((2 * Real.pi : ℝ) : ℂ)) * q ^ 2 * (rr p + aa p) := by
    intro p
    rw [finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand,
      finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceAngularTraceIntegral_eq_radialCoefficient,
      finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient_eq_denominatorForm]
    dsimp [q, pref, alpha, beta, rx, ry, rr, aa]
    rw [finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand,
      finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficient_eq_denominatorForm,
      finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand,
      finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficient_eq_denominatorForm]
    simp [finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumerator,
      inPlaneRotationCoefficient]
    field_simp [hpref]
    ring
  have hrx : IntervalIntegrable rx volume 0 pMax := by
    simpa [rx] using
      intervalIntegrable_finiteBroadeningCurrentRungRadialIntegrand
        .x .x v m probeEnergy broadening disorderStrength hbar pMax
        hbroadening hdisorder.le hpMax
  have hry : IntervalIntegrable ry volume 0 pMax := by
    simpa [ry] using
      intervalIntegrable_finiteBroadeningCurrentRungRadialIntegrand
        .y .x v m probeEnergy broadening disorderStrength hbar pMax
        hbroadening hdisorder.le hpMax
  have hrr : IntervalIntegrable rr volume 0 pMax := by
    have hden : ∀ p : ℝ,
        finiteCutoffContinuumBornDysonDenominator
          .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax ≠ 0 := fun p =>
      finiteCutoffContinuumBornDysonDenominator_ne_zero
        .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
        hbroadening hdisorder.le hpMax
    apply Continuous.intervalIntegrable
    exact ((Complex.continuous_ofReal.comp continuous_id).mul
      ((by
        unfold finiteCutoffContinuumBornDysonDenominator
        fun_prop : Continuous (fun p : ℝ =>
          finiteCutoffContinuumBornDysonDenominator
            .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax)).inv₀ hden).pow 2).mul
      continuous_const
  have haa : IntervalIntegrable aa volume 0 pMax := by
    have hden : ∀ p : ℝ,
        finiteCutoffContinuumBornDysonDenominator
          .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax ≠ 0 := fun p =>
      finiteCutoffContinuumBornDysonDenominator_ne_zero
        .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
        hbroadening hdisorder.le hpMax
    apply Continuous.intervalIntegrable
    exact ((Complex.continuous_ofReal.comp continuous_id).mul
      ((by
        unfold finiteCutoffContinuumBornDysonDenominator
        fun_prop : Continuous (fun p : ℝ =>
          finiteCutoffContinuumBornDysonDenominator
            .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax)).inv₀ hden).pow 2).mul
      continuous_const
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral
  rw [intervalIntegral.integral_congr hpointwise]
  rw [intervalIntegral.integral_sub
    (((hrx.const_mul alpha).sub (hry.const_mul beta)).const_mul (2 * q ^ 2 * pref⁻¹))
    ((hrr.add haa).const_mul ((((2 * Real.pi : ℝ) : ℂ)) * q ^ 2))]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (hrx.const_mul alpha) (hry.const_mul beta),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hrr haa]
  rw [show (∫ p in (0 : ℝ)..pMax, rr p) =
      finiteBroadeningSameSideRadialEndpoint
        .retarded v m probeEnergy broadening disorderStrength hbar pMax by
    simpa [rr] using
      integral_finiteBroadeningSameSide_eq_endpoint
        .retarded v m probeEnergy broadening disorderStrength hbar pMax
        hvelocity hbroadening hdisorder.le hpMax]
  rw [show (∫ p in (0 : ℝ)..pMax, aa p) =
      finiteBroadeningSameSideRadialEndpoint
        .advanced v m probeEnergy broadening disorderStrength hbar pMax by
    simpa [aa] using
      integral_finiteBroadeningSameSide_eq_endpoint
        .advanced v m probeEnergy broadening disorderStrength hbar pMax
        hvelocity hbroadening hdisorder.le hpMax]
  simp [finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient,
    finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceMomentumIntegralReduced,
    q, pref, alpha, beta, rx, ry]

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
      (fun broadening : ℝ =>
        finiteBroadeningSameSideRadialEndpoint
          side v m probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (zeroBroadeningSameSideRadialEndpoint
          side v m probeEnergy disorderStrength hbar pMax)) := by
  have hE := tendsto_finiteCutoffContinuumBornEffectiveEnergy_broadening_zero
    side v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hM := tendsto_finiteCutoffContinuumBornEffectiveMass_broadening_zero
    side v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hA := (hE.mul hE).sub (hM.mul hM)
  have hD0 := tendsto_finiteCutoffContinuumBornDysonDenominator_broadening_zero
    side v m 0 probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hDMax := tendsto_finiteCutoffContinuumBornDysonDenominator_broadening_zero
    side v m pMax probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hconst : Tendsto (fun _ : ℝ => ((((2 * v ^ 2 : ℝ) : ℂ))⁻¹))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((((2 * v ^ 2 : ℝ) : ℂ))⁻¹)) := tendsto_const_nhds
  simpa [finiteBroadeningSameSideRadialEndpoint, zeroBroadeningSameSideRadialEndpoint,
    radialQuadraticInverseSquareEndpoint,
    finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary] using
    (hconst.mul hA).mul ((hDMax.inv₀ hdenMax).sub (hD0.inv₀ hden0))

/-- At fixed positive disorder and finite cutoff, the proof-independent reduced longitudinal Středa
radial response converges as `η → 0⁺`. The only extra same-side regularity needed beyond the existing
RA-rung hypotheses is nonvanishing of the zero-broadening Dyson denominator at the two radial
endpoints. -/
theorem tendsto_finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceMomentumIntegralReduced_broadening_zero
    (e v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hpMax : 0 ≤ pMax) (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hdisorder : 0 < disorderStrength) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2)
    (hrenorm : finiteCutoffContinuumBornBoundaryRealRenormalization
      v m probeEnergy disorderStrength hbar pMax < 1)
    (hdet : finiteCutoffContinuumBornDysonLadderDeterminantZeroBroadeningBoundary
      v m probeEnergy disorderStrength hbar pMax ≠ 0)
    (hden0 : ∀ side : SpectralSide,
      finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
        side v m 0 probeEnergy disorderStrength hbar pMax ≠ 0)
    (hdenMax : ∀ side : SpectralSide,
      finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
        side v m pMax probeEnergy disorderStrength hbar pMax ≠ 0) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceMomentumIntegralReduced
          e v m probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceMomentumIntegralZeroBroadeningBoundary
          e v m probeEnergy disorderStrength hbar pMax)) := by
  have hAlpha :=
    tendsto_finiteCutoffContinuumBornDysonLadderSolvedCoefficient_broadening_zero_of_boundary_realRenormalization_lt_one
      .x v m probeEnergy disorderStrength hbar pMax hpMax hvelocity hhbar
      hdisorder hmetal hcutoff hrenorm hdet
  have hBeta :=
    tendsto_finiteCutoffContinuumBornDysonLadderSolvedCoefficient_broadening_zero_of_boundary_realRenormalization_lt_one
      .y v m probeEnergy disorderStrength hbar pMax hpMax hvelocity hhbar
      hdisorder hmetal hcutoff hrenorm hdet
  have hKx :=
    tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient_broadening_zero_of_boundary_realRenormalization_lt_one
      .x .x v m probeEnergy disorderStrength hbar pMax hpMax hvelocity hhbar
      hdisorder hmetal hcutoff hrenorm
  have hKy :=
    tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient_broadening_zero_of_boundary_realRenormalization_lt_one
      .y .x v m probeEnergy disorderStrength hbar pMax hpMax hvelocity hhbar
      hdisorder hmetal hcutoff hrenorm
  have hRR := tendsto_finiteBroadeningSameSideRadialEndpoint_broadening_zero
    .retarded v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
    (hden0 .retarded) (hdenMax .retarded)
  have hAA := tendsto_finiteBroadeningSameSideRadialEndpoint_broadening_zero
    .advanced v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
    (hden0 .advanced) (hdenMax .advanced)
  exact
    (((hAlpha.mul hKx).sub (hBeta.mul hKy)).const_mul
        (2 * ((((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))) ^ 2 *
          (((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ))⁻¹)).sub
      ((hRR.add hAA).const_mul
        ((((2 * Real.pi : ℝ) : ℂ)) *
          ((((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))) ^ 2)) |>.simpa
        [finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceMomentumIntegralReduced,
          finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceMomentumIntegralZeroBroadeningBoundary,
          mul_assoc]

end

end QuantumTheory.Transport.Models.MassiveDirac
