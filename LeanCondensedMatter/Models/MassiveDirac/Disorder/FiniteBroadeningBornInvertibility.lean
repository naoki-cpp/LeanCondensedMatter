import LeanCondensedMatter.Analysis.Operator.Spectral.DissipativeShift
import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.Denominator
import LeanCondensedMatter.Transport.Analysis.ContinuumMeasure
import LeanCondensedMatter.Models.MassiveDirac.Disorder.FiniteBroadeningBornDysonShift
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite-broadening Born-Dyson invertibility

For nonzero external broadening, nonnegative scalar-disorder strength, and a nonnegative radial
cutoff, the finite-cutoff continuum Born self-energy is dissipative with the sign selected by the
spectral regulator. Consequently the corresponding Born-Dyson shift has trivial kernel. Since the
massive-Dirac Hilbert space is finite-dimensional, the shift is a unit, and its explicit Pauli
quadratic denominator is nonzero at every momentum.

This closes the invertibility boundary of the finite-`η` Born-Dyson propagator. No equality with the
exact disorder average, SCBA closure, Ward identity, or broadening/disorder limit is asserted here.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport
open scoped Interval

private theorem im_inner_self_pauliGreenOperatorOfRegulator_apply
    (v m px py probeEnergy regulator : ℝ) (hregulator : regulator ≠ 0)
    (ψ : DiracHilbert) :
    (inner ℂ ψ
      (pauliGreenOperatorOfRegulator v m px py probeEnergy regulator ψ)).im =
      -(regulator *
        ‖pauliGreenOperatorOfRegulator v m px py probeEnergy regulator ψ‖ ^ 2) := by
  have hcanonical :=
    im_inner_resolvent_spectralParameterOfRegulator_apply_self
      (hamiltonianOperator v m px py)
      (hamiltonianOperator_isSelfAdjoint v m px py)
      probeEnergy regulator hregulator ψ
  rw [resolvent_spectralParameterOfRegulator_eq_pauliGreenOperatorOfRegulator
    v m px py probeEnergy regulator hregulator] at hcanonical
  have hsymm := inner_im_symm (𝕜 := ℂ)
    (pauliGreenOperatorOfRegulator v m px py probeEnergy regulator ψ) ψ
  change
    (inner ℂ
      (pauliGreenOperatorOfRegulator v m px py probeEnergy regulator ψ) ψ).im =
      -(inner ℂ ψ
        (pauliGreenOperatorOfRegulator v m px py probeEnergy regulator ψ)).im at hsymm
  rw [hcanonical] at hsymm
  linarith

private noncomputable def continuumBornRadialDissipationDensity
    (v m probeEnergy regulator : ℝ) (ψ : DiracHilbert) (p : ℝ) : ℝ :=
  p / 2 *
    (‖pauliGreenOperatorOfRegulator v m p 0 probeEnergy regulator ψ‖ ^ 2 +
      ‖pauliGreenOperatorOfRegulator v m (-p) 0 probeEnergy regulator ψ‖ ^ 2)

private theorem continuumBornRadialDissipationDensity_nonneg
    (v m probeEnergy regulator : ℝ) (ψ : DiracHilbert) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ continuumBornRadialDissipationDensity v m probeEnergy regulator ψ p := by
  unfold continuumBornRadialDissipationDensity
  positivity

private theorem im_inner_self_inversionSymmetrizedPauliGreenOperatorOfRegulator_apply
    (v m probeEnergy regulator p : ℝ) (hregulator : regulator ≠ 0)
    (ψ : DiracHilbert) :
    (inner ℂ ψ
      (inversionSymmetrizedPauliGreenOperatorOfRegulator
        v m p 0 probeEnergy regulator ψ)).im =
      -(regulator / 2 *
        (‖pauliGreenOperatorOfRegulator v m p 0 probeEnergy regulator ψ‖ ^ 2 +
          ‖pauliGreenOperatorOfRegulator v m (-p) 0 probeEnergy regulator ψ‖ ^ 2)) := by
  rw [inversionSymmetrizedPauliGreenOperatorOfRegulator]
  simp only [smul_apply, add_apply, inner_smul_right, inner_add_right,
    Complex.add_im, Complex.mul_im]
  norm_num
  rw [im_inner_self_pauliGreenOperatorOfRegulator_apply
      v m p 0 probeEnergy regulator hregulator ψ,
    im_inner_self_pauliGreenOperatorOfRegulator_apply
      v m (-p) 0 probeEnergy regulator hregulator ψ]
  ring

private theorem im_inner_self_continuumBornRadialGreenKernelOfRegulator_apply
    (v m probeEnergy regulator p : ℝ) (hregulator : regulator ≠ 0)
    (ψ : DiracHilbert) :
    (inner ℂ ψ
      (continuumBornRadialGreenKernelOfRegulator
        v m probeEnergy regulator p ψ)).im =
      -(regulator *
        continuumBornRadialDissipationDensity v m probeEnergy regulator ψ p) := by
  rw [continuumBornRadialGreenKernelOfRegulator]
  simp only [smul_apply, inner_smul_right, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  rw [im_inner_self_inversionSymmetrizedPauliGreenOperatorOfRegulator_apply
    v m probeEnergy regulator p hregulator ψ]
  unfold continuumBornRadialDissipationDensity
  ring

private theorem im_inner_self_finiteCutoffContinuumBornGreenIntegralOfRegulator_apply
    (v m probeEnergy regulator pMax : ℝ) (hregulator : regulator ≠ 0)
    (ψ : DiracHilbert) :
    (inner ℂ ψ
      (finiteCutoffContinuumBornGreenIntegralOfRegulator
        v m probeEnergy regulator pMax ψ)).im =
      -regulator *
        ∫ p in (0 : ℝ)..pMax,
          continuumBornRadialDissipationDensity v m probeEnergy regulator ψ p := by
  let eval :
      (DiracHilbert →L[ℂ] DiracHilbert) →L[ℂ] DiracHilbert :=
    ContinuousLinearMap.apply ℂ DiracHilbert ψ
  let L : (DiracHilbert →L[ℂ] DiracHilbert) →L[ℂ] ℂ :=
    (innerSL ℂ ψ).comp eval
  have hkernel : Continuous
      (continuumBornRadialGreenKernelOfRegulator v m probeEnergy regulator) :=
    continuous_continuumBornRadialGreenKernelOfRegulator
      v m probeEnergy regulator hregulator
  have hint : IntervalIntegrable
      (continuumBornRadialGreenKernelOfRegulator v m probeEnergy regulator)
      volume 0 pMax := hkernel.intervalIntegrable 0 pMax
  have hmap := ContinuousLinearMap.intervalIntegral_comp_comm L hint
  have hLint : IntervalIntegrable
      (fun p : ℝ =>
        L (continuumBornRadialGreenKernelOfRegulator v m probeEnergy regulator p))
      volume 0 pMax :=
    (L.continuous.comp hkernel).intervalIntegrable 0 pMax
  have hquad :
      (inner ℂ ψ
        (finiteCutoffContinuumBornGreenIntegralOfRegulator
          v m probeEnergy regulator pMax ψ)).im =
        ∫ p in (0 : ℝ)..pMax,
          (inner ℂ ψ
            (continuumBornRadialGreenKernelOfRegulator
              v m probeEnergy regulator p ψ)).im := by
    unfold finiteCutoffContinuumBornGreenIntegralOfRegulator
    change (L (∫ p in (0 : ℝ)..pMax,
      continuumBornRadialGreenKernelOfRegulator
        v m probeEnergy regulator p)).im = _
    calc
      _ = (∫ p in (0 : ℝ)..pMax,
          L (continuumBornRadialGreenKernelOfRegulator
            v m probeEnergy regulator p)).im := congrArg Complex.im hmap.symm
      _ = ∫ p in (0 : ℝ)..pMax,
          (L (continuumBornRadialGreenKernelOfRegulator
            v m probeEnergy regulator p)).im :=
            (intervalIntegral.intervalIntegral_im hLint).symm
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro p _
        simp [L, eval]
  rw [hquad, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro p _
  change
    (inner ℂ ψ
      (continuumBornRadialGreenKernelOfRegulator
        v m probeEnergy regulator p ψ)).im =
      -regulator * continuumBornRadialDissipationDensity
        v m probeEnergy regulator ψ p
  simpa only [neg_mul] using
    im_inner_self_continuumBornRadialGreenKernelOfRegulator_apply
      v m probeEnergy regulator p hregulator ψ

private theorem regulator_mul_im_inner_self_finiteCutoffContinuumBornGreenIntegralOfRegulator_apply_nonpos
    (v m probeEnergy regulator pMax : ℝ) (hregulator : regulator ≠ 0)
    (hpMax : 0 ≤ pMax) (ψ : DiracHilbert) :
    regulator *
      (inner ℂ ψ
        (finiteCutoffContinuumBornGreenIntegralOfRegulator
          v m probeEnergy regulator pMax ψ)).im ≤ 0 := by
  have hdensity :
      0 ≤ ∫ p in (0 : ℝ)..pMax,
        continuumBornRadialDissipationDensity v m probeEnergy regulator ψ p := by
    exact intervalIntegral.integral_nonneg hpMax fun p hp =>
      continuumBornRadialDissipationDensity_nonneg
        v m probeEnergy regulator ψ hp.1
  rw [im_inner_self_finiteCutoffContinuumBornGreenIntegralOfRegulator_apply
    v m probeEnergy regulator pMax hregulator ψ]
  calc
    regulator *
        (-regulator *
          ∫ p in (0 : ℝ)..pMax,
            continuumBornRadialDissipationDensity v m probeEnergy regulator ψ p) =
      -(regulator ^ 2 *
        ∫ p in (0 : ℝ)..pMax,
          continuumBornRadialDissipationDensity v m probeEnergy regulator ψ p) := by ring
    _ ≤ 0 := neg_nonpos.mpr (mul_nonneg (sq_nonneg regulator) hdensity)

/-- The arbitrary-regulator finite-cutoff continuum Born self-energy is dissipative: in the
physicists' quadratic-form orientation `⟪ψ,Σψ⟫`, its imaginary part has sign opposite to the signed
spectral regulator. -/
theorem finiteCutoffContinuumBornSelfEnergyOfRegulator_dissipative
    (v m probeEnergy regulator disorderStrength hbar pMax : ℝ)
    (hregulator : regulator ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) (ψ : DiracHilbert) :
    regulator *
      (inner ℂ ψ
        (finiteCutoffContinuumBornSelfEnergyOfRegulator
          v m probeEnergy regulator disorderStrength hbar pMax ψ)).im ≤ 0 := by
  have hpref : 0 ≤ fullAngleMomentumMeasurePrefactor hbar := by
    unfold fullAngleMomentumMeasurePrefactor momentumMeasurePrefactor
    positivity
  have hscale : 0 ≤ disorderStrength * fullAngleMomentumMeasurePrefactor hbar :=
    mul_nonneg hdisorder hpref
  have hgreen :=
    regulator_mul_im_inner_self_finiteCutoffContinuumBornGreenIntegralOfRegulator_apply_nonpos
      v m probeEnergy regulator pMax hregulator hpMax ψ
  unfold finiteCutoffContinuumBornSelfEnergyOfRegulator
  simp only [smul_apply, inner_smul_right, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  calc
    regulator *
        ((disorderStrength * fullAngleMomentumMeasurePrefactor hbar) *
          (inner ℂ ψ
            (finiteCutoffContinuumBornGreenIntegralOfRegulator
              v m probeEnergy regulator pMax ψ)).im) =
      (disorderStrength * fullAngleMomentumMeasurePrefactor hbar) *
        (regulator *
          (inner ℂ ψ
            (finiteCutoffContinuumBornGreenIntegralOfRegulator
              v m probeEnergy regulator pMax ψ)).im) := by ring
    _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hscale hgreen

private theorem finiteCutoffContinuumBornDysonShiftOperator_injective
    (side : SpectralSide)
    (v m px py probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    Function.Injective
      (finiteCutoffContinuumBornDysonShiftOperator
        side v m px py probeEnergy broadening disorderStrength hbar pMax) := by
  have hreg : (spectralParameter side probeEnergy broadening).im ≠ 0 := by
    rw [spectralParameter_im]
    exact side.regulator_ne_zero hbroadening
  have hdiss : ∀ ψ : DiracHilbert,
      (spectralParameter side probeEnergy broadening).im *
        (inner ℂ ψ (finiteCutoffContinuumBornSelfEnergy
          side v m probeEnergy broadening disorderStrength hbar pMax ψ)).im ≤ 0 := by
    intro ψ
    simpa [spectralParameter_im, finiteCutoffContinuumBornSelfEnergy] using
      finiteCutoffContinuumBornSelfEnergyOfRegulator_dissipative
        v m probeEnergy (side.regulator broadening) disorderStrength hbar pMax
        (side.regulator_ne_zero hbroadening) hdisorder hpMax ψ
  simpa only [finiteCutoffContinuumBornDysonShiftOperator] using
    QuantumTheory.dissipativeSpectralShift_injective
      (hamiltonianOperator v m px py)
      (finiteCutoffContinuumBornSelfEnergy
        side v m probeEnergy broadening disorderStrength hbar pMax)
      (hamiltonianOperator_isSelfAdjoint v m px py)
      (spectralParameter side probeEnergy broadening) hreg hdiss

/-- In the finite-broadening regime with nonnegative scalar disorder and radial cutoff, the
finite-cutoff Born-Dyson quadratic denominator is nonzero at every momentum. -/
theorem finiteCutoffContinuumBornDysonDenominator_ne_zero
    (side : SpectralSide)
    (v m px py probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    finiteCutoffContinuumBornDysonDenominator
      side v m px py probeEnergy broadening disorderStrength hbar pMax ≠ 0 := by
  let M := finiteCutoffContinuumBornDysonShiftMatrix
    side v m px py probeEnergy broadening disorderStrength hbar pMax
  let shift := finiteCutoffContinuumBornDysonShiftOperator
    side v m px py probeEnergy broadening disorderStrength hbar pMax
  have hinj : Function.Injective shift :=
    finiteCutoffContinuumBornDysonShiftOperator_injective
      side v m px py probeEnergy broadening disorderStrength hbar pMax
      hbroadening hdisorder hpMax
  have hshiftUnit : IsUnit shift :=
    ContinuousLinearMap.isUnit_iff_bijective.mpr
      ⟨hinj, LinearMap.surjective_of_injective (f := shift.toLinearMap) hinj⟩
  have hoperatorUnit : IsUnit (matrixOperator M) := by
    rw [← finiteCutoffContinuumBornDysonShiftOperator_eq_matrix
      side v m px py probeEnergy broadening disorderStrength hbar pMax hbroadening]
    exact hshiftUnit
  let φ : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert) := Matrix.toEuclideanCLM
  have hmatrixUnit : IsUnit M := by
    apply (isUnit_map_iff φ M).mp
    simpa [φ, matrixOperator] using hoperatorUnit
  have hdet : M.det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det M).mp hmatrixUnit)
  simpa only [M, finiteCutoffContinuumBornDysonShiftMatrix_det] using hdet


/-- The finite-broadening retarded and advanced massive-Dirac Dyson spectral
centers are distinct in the metallic-center region. The real part of the
retarded center is positive, so if its imaginary part vanished there would
be a pole at real momentum. Dyson invertibility excludes that pole; spectral
conjugation then makes the advanced-minus-retarded center gap nonzero.
No zero-broadening, disorder, or cutoff limit is taken. -/
theorem finiteCutoffContinuumBornDysonRadial_center_gap_ne_zero_of_re_pos
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hbroadening : broadening ≠ 0)
    (hdisorder : 0 ≤ disorderStrength) (hpMax : 0 ≤ pMax)
    (hcenterR : 0 <
      (finiteCutoffContinuumBornEffectiveEnergy
          .retarded v m probeEnergy broadening disorderStrength hbar pMax ^ 2 -
        finiteCutoffContinuumBornEffectiveMass
          .retarded v m probeEnergy broadening disorderStrength hbar pMax ^ 2).re) :
    (finiteCutoffContinuumBornEffectiveEnergy
        .advanced v m probeEnergy broadening disorderStrength hbar pMax ^ 2 -
      finiteCutoffContinuumBornEffectiveMass
        .advanced v m probeEnergy broadening disorderStrength hbar pMax ^ 2) -
    (finiteCutoffContinuumBornEffectiveEnergy
        .retarded v m probeEnergy broadening disorderStrength hbar pMax ^ 2 -
      finiteCutoffContinuumBornEffectiveMass
        .retarded v m probeEnergy broadening disorderStrength hbar pMax ^ 2) ≠ 0 := by
  let energyR := finiteCutoffContinuumBornEffectiveEnergy
    .retarded v m probeEnergy broadening disorderStrength hbar pMax
  let energyA := finiteCutoffContinuumBornEffectiveEnergy
    .advanced v m probeEnergy broadening disorderStrength hbar pMax
  let massR := finiteCutoffContinuumBornEffectiveMass
    .retarded v m probeEnergy broadening disorderStrength hbar pMax
  let massA := finiteCutoffContinuumBornEffectiveMass
    .advanced v m probeEnergy broadening disorderStrength hbar pMax
  have hden (p : ℝ) : massiveDiracRadialDenominator v p energyR massR ≠ 0 := by
    rw [finiteCutoffContinuumBornDysonDenominator_eq_radial]
    exact finiteCutoffContinuumBornDysonDenominator_ne_zero
      .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
      hbroadening hdisorder hpMax
  have him : (energyR ^ 2 - massR ^ 2).im ≠ 0 :=
    massiveDiracRadialDenominator_center_im_ne_zero_of_re_pos
      v energyR massR hvelocity hcenterR hden
  have hstar : star (energyR ^ 2 - massR ^ 2) = energyA ^ 2 - massA ^ 2 := by
    have hx := star_finiteCutoffContinuumBornDysonDenominator
      .retarded v m 0 0 probeEnergy broadening disorderStrength hbar pMax hbroadening
    simpa [finiteCutoffContinuumBornDysonDenominator, SpectralSide.opposite,
      energyR, energyA, massR, massA] using hx
  intro hgap
  have heq : energyA ^ 2 - massA ^ 2 = energyR ^ 2 - massR ^ 2 :=
    sub_eq_zero.mp hgap
  have hs : star (energyR ^ 2 - massR ^ 2) = energyR ^ 2 - massR ^ 2 :=
    hstar.trans heq
  have hstarIm (z : ℂ) : (star z).im = -z.im := by simp
  have himZero : (energyR ^ 2 - massR ^ 2).im = 0 := by
    have h := congrArg Complex.im hs
    rw [hstarIm] at h
    linarith
  exact him himZero

end

end QuantumTheory.Models.MassiveDirac
