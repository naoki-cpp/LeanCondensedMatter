import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderRadialDenominator
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningLadderZeroBroadening
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningBornInvertibility
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Massive-Dirac longitudinal same-side Středa remainder

This module owns the bare-source `RR/AA` same-side radial remainder used by the longitudinal
Massive-Dirac Středa response. It evaluates the finite-broadening radial integral, exposes its
fixed-disorder `η → 0⁺` endpoint, and records the separate weak-disorder behavior of that endpoint.

The same-side remainder stays separate from the singular retarded-advanced ladder action. The cutoff
remains fixed throughout, and no physical conductivity normalization is attached here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter MeasureTheory QuantumTheory.Transport
open scoped Interval

private theorem intervalIntegrable_and_integral_radialQuadraticInverseSquare
    (v pMax : ℝ) (A : ℂ) (hvelocity : v ≠ 0)
    (hden : ∀ p : ℝ, A - ((v ^ 2 * p ^ 2 : ℝ) : ℂ) ≠ 0) :
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

/-- Evaluated finite-broadening radial endpoint of one bare-source same-side spectral branch. -/
def finiteBroadeningSameSideRadialEndpoint
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

/-- Fixed-disorder zero-broadening endpoint of one bare-source same-side spectral branch. -/
def zeroBroadeningSameSideRadialEndpoint
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

/-- The finite-broadening bare-source same-side radial integrand is integrable and evaluates to the
canonical endpoint. -/
theorem finiteBroadeningSameSide_integrable_and_integral_eq_endpoint
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

/-- At fixed disorder and cutoff, the finite-broadening same-side endpoint converges to its
zero-broadening boundary along positive broadening. -/
theorem tendsto_finiteBroadeningSameSideRadialEndpoint_broadening_zero
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

/-- With the metallic shell strictly inside the fixed cutoff, the zero-broadening same-side endpoint
is continuous at zero disorder. -/
theorem continuousAt_zeroBroadeningSameSideRadialEndpoint_disorder_zero
    (side : SpectralSide) (v m probeEnergy hbar pMax : ℝ)
    (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    ContinuousAt
      (fun disorderStrength : ℝ =>
        zeroBroadeningSameSideRadialEndpoint
          side v m probeEnergy disorderStrength hbar pMax) 0 := by
  have hgap : 0 < probeEnergy ^ 2 - m ^ 2 := by
    have hprobe : 0 < probeEnergy := lt_of_le_of_lt (abs_nonneg m) hmetal
    rw [← sq_abs m]
    nlinarith [abs_nonneg m]
  have hmax : probeEnergy ^ 2 - m ^ 2 - v ^ 2 * pMax ^ 2 < 0 := by
    linarith
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
  unfold zeroBroadeningSameSideRadialEndpoint
  exact (continuousAt_const.mul ((hE.pow 2).sub (hM.pow 2))).mul
    ((hDMax.inv₀ hdenMax).sub (hD0.inv₀ hden0))

/-- The zero-broadening same-side endpoint stays finite as disorder vanishes, so multiplying it by
the disorder strength sends it to zero. -/
theorem tendsto_disorderStrength_mul_zeroBroadeningSameSideRadialEndpoint_disorder_zero
    (side : SpectralSide) (v m probeEnergy hbar pMax : ℝ)
    (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun disorderStrength : ℝ =>
        (disorderStrength : ℂ) *
          zeroBroadeningSameSideRadialEndpoint
            side v m probeEnergy disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hl : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0 := by
    exact inf_le_left
  have hWReal : Tendsto (fun disorderStrength : ℝ => disorderStrength)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    continuousAt_id.tendsto.mono_left hl
  have hW := hWReal.ofReal
  simpa using hW.mul
    ((continuousAt_zeroBroadeningSameSideRadialEndpoint_disorder_zero
      side v m probeEnergy hbar pMax hmetal hcutoff).tendsto.mono_left hl)

end

end QuantumTheory.Transport.Models.MassiveDirac
