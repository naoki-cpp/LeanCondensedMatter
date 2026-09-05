import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningBornPropagator
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

namespace AnomalousHall.MassiveDirac

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
  have h :=
    im_inner_self_resolvent_spectralParameterOfRegulator_apply
      (hamiltonianOperator v m px py)
      (hamiltonianOperator_isSelfAdjoint v m px py)
      probeEnergy regulator hregulator ψ
  rw [resolvent_spectralParameterOfRegulator_eq_pauliGreenOperatorOfRegulator
    v m px py probeEnergy regulator hregulator] at h
  exact h

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

private theorem continuous_continuumBornRadialGreenKernelForDissipation
    (v m probeEnergy regulator : ℝ) (hregulator : regulator ≠ 0) :
    Continuous
      (continuumBornRadialGreenKernelOfRegulator v m probeEnergy regulator) := by
  have hscalar : Continuous
      (continuumBornRadialScalarIntegrandOfRegulator v m probeEnergy regulator) := by
    unfold continuumBornRadialScalarIntegrandOfRegulator
      pauliGreenScalarCoefficientOfRegulator
    exact (Complex.continuous_ofReal.comp continuous_id).mul
      ((continuous_inv_pauliGreenDenominatorOfRegulator_radial
        v m probeEnergy regulator hregulator).mul continuous_const)
  have hz : Continuous
      (continuumBornRadialZIntegrandOfRegulator v m probeEnergy regulator) := by
    unfold continuumBornRadialZIntegrandOfRegulator pauliGreenZCoefficientOfRegulator
    exact (Complex.continuous_ofReal.comp continuous_id).mul
      ((continuous_inv_pauliGreenDenominatorOfRegulator_radial
        v m probeEnergy regulator hregulator).mul continuous_const)
  rw [show continuumBornRadialGreenKernelOfRegulator v m probeEnergy regulator =
      fun p : ℝ =>
        continuumBornRadialScalarIntegrandOfRegulator v m probeEnergy regulator p •
            (1 : DiracHilbert →L[ℂ] DiracHilbert) +
          continuumBornRadialZIntegrandOfRegulator v m probeEnergy regulator p •
            matrixOperator sigmaZ by
    funext p
    exact continuumBornRadialGreenKernelOfRegulator_eq v m probeEnergy regulator p]
  exact (hscalar.smul continuous_const).add (hz.smul continuous_const)

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
    continuous_continuumBornRadialGreenKernelForDissipation
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
    calc
      (inner ℂ ψ
          ((∫ p in (0 : ℝ)..pMax,
            continuumBornRadialGreenKernelOfRegulator
              v m probeEnergy regulator p) ψ)).im =
          (L (∫ p in (0 : ℝ)..pMax,
            continuumBornRadialGreenKernelOfRegulator
              v m probeEnergy regulator p)).im := by
            simp [L, eval]
      _ = (∫ p in (0 : ℝ)..pMax,
          L (continuumBornRadialGreenKernelOfRegulator
            v m probeEnergy regulator p)).im := by rw [hmap]
      _ = ∫ p in (0 : ℝ)..pMax,
          (L (continuumBornRadialGreenKernelOfRegulator
            v m probeEnergy regulator p)).im := by
            exact (intervalIntegral.intervalIntegral_im hLint).symm
      _ = ∫ p in (0 : ℝ)..pMax,
          (inner ℂ ψ
            (continuumBornRadialGreenKernelOfRegulator
              v m probeEnergy regulator p ψ)).im := by
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
  exact im_inner_self_continuumBornRadialGreenKernelOfRegulator_apply
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
  have hpref : 0 ≤ continuumBornAngularMeasurePrefactor hbar := by
    unfold continuumBornAngularMeasurePrefactor momentumMeasurePrefactor
    positivity
  have hscale : 0 ≤ disorderStrength * continuumBornAngularMeasurePrefactor hbar :=
    mul_nonneg hdisorder hpref
  have hgreen :=
    regulator_mul_im_inner_self_finiteCutoffContinuumBornGreenIntegralOfRegulator_apply_nonpos
      v m probeEnergy regulator pMax hregulator hpMax ψ
  unfold finiteCutoffContinuumBornSelfEnergyOfRegulator
  simp only [smul_apply, inner_smul_right, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  calc
    regulator *
        ((disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
          (inner ℂ ψ
            (finiteCutoffContinuumBornGreenIntegralOfRegulator
              v m probeEnergy regulator pMax ψ)).im) =
      (disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
        (regulator *
          (inner ℂ ψ
            (finiteCutoffContinuumBornGreenIntegralOfRegulator
              v m probeEnergy regulator pMax ψ)).im) := by ring
    _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hscale hgreen

private theorem finiteCutoffContinuumBornSelfEnergy_dissipative
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) (ψ : DiracHilbert) :
    side.regulator broadening *
      (inner ℂ ψ
        (finiteCutoffContinuumBornSelfEnergy
          side v m probeEnergy broadening disorderStrength hbar pMax ψ)).im ≤ 0 := by
  simpa [finiteCutoffContinuumBornSelfEnergy] using
    finiteCutoffContinuumBornSelfEnergyOfRegulator_dissipative
      v m probeEnergy (side.regulator broadening) disorderStrength hbar pMax
      (side.regulator_ne_zero hbroadening) hdisorder hpMax ψ

private theorem finiteCutoffContinuumBornDysonShiftOperator_injective
    (side : SpectralSide)
    (v m px py probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    Function.Injective
      (finiteCutoffContinuumBornDysonShiftOperator
        side v m px py probeEnergy broadening disorderStrength hbar pMax) := by
  let shift := finiteCutoffContinuumBornDysonShiftOperator
    side v m px py probeEnergy broadening disorderStrength hbar pMax
  intro ψ φ hψφ
  have hsub : shift (ψ - φ) = 0 := by
    rw [map_sub, hψφ, sub_self]
  have hzero : ψ - φ = 0 := by
    by_contra hne
    have hnorm : 0 < ‖ψ - φ‖ ^ 2 := by
      exact sq_pos_of_pos (norm_pos_iff.mpr hne)
    have hreg : side.regulator broadening ≠ 0 :=
      side.regulator_ne_zero hbroadening
    have hregSq : 0 < (side.regulator broadening) ^ 2 :=
      sq_pos_of_ne_zero hreg
    have hSigma := finiteCutoffContinuumBornSelfEnergy_dissipative
      side v m probeEnergy broadening disorderStrength hbar pMax
      hbroadening hdisorder hpMax (ψ - φ)
    have hshiftApply :
        spectralParameter side probeEnergy broadening • (ψ - φ) -
            hamiltonianOperator v m px py (ψ - φ) -
            finiteCutoffContinuumBornSelfEnergy
              side v m probeEnergy broadening disorderStrength hbar pMax (ψ - φ) = 0 := by
      simpa [shift, finiteCutoffContinuumBornDysonShiftOperator,
        Algebra.algebraMap_eq_smul_one] using hsub
    have hH :
        (inner ℂ (ψ - φ) (hamiltonianOperator v m px py (ψ - φ))).im = 0 := by
      exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
        (hamiltonianOperator_isSelfAdjoint v m px py)).im_inner_self_apply (ψ - φ)
    have himSelf : (inner ℂ (ψ - φ) (ψ - φ)).im = 0 :=
      inner_self_im (𝕜 := ℂ) (ψ - φ)
    have hreSelf : (inner ℂ (ψ - φ) (ψ - φ)).re = ‖ψ - φ‖ ^ 2 :=
      (norm_sq_eq_re_inner (𝕜 := ℂ) (ψ - φ)).symm
    have him := congrArg
      (fun w : DiracHilbert => (inner ℂ (ψ - φ) w).im) hshiftApply
    rw [inner_sub_right, inner_sub_right, inner_smul_right] at him
    simp only [Complex.sub_im, Complex.mul_im, spectralParameter_re, spectralParameter_im,
      himSelf, hreSelf, hH, mul_zero, zero_add, sub_zero] at him
    have hbalance :
        side.regulator broadening * ‖ψ - φ‖ ^ 2 =
          (inner ℂ (ψ - φ)
            (finiteCutoffContinuumBornSelfEnergy
              side v m probeEnergy broadening disorderStrength hbar pMax (ψ - φ))).im := by
      simpa using him
    rw [← hbalance] at hSigma
    have hpositive :
        0 < (side.regulator broadening) ^ 2 * ‖ψ - φ‖ ^ 2 :=
      mul_pos hregSq hnorm
    have hrewrite :
        side.regulator broadening *
            (side.regulator broadening * ‖ψ - φ‖ ^ 2) =
          (side.regulator broadening) ^ 2 * ‖ψ - φ‖ ^ 2 := by ring
    rw [hrewrite] at hSigma
    linarith
  exact sub_eq_zero.mp hzero

private theorem finiteCutoffContinuumBornDysonShiftOperator_isUnit
    (side : SpectralSide)
    (v m px py probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    IsUnit
      (finiteCutoffContinuumBornDysonShiftOperator
        side v m px py probeEnergy broadening disorderStrength hbar pMax) := by
  let shift := finiteCutoffContinuumBornDysonShiftOperator
    side v m px py probeEnergy broadening disorderStrength hbar pMax
  have hinj : Function.Injective shift := by
    exact finiteCutoffContinuumBornDysonShiftOperator_injective
      side v m px py probeEnergy broadening disorderStrength hbar pMax
      hbroadening hdisorder hpMax
  have hsurj : Function.Surjective shift := by
    exact LinearMap.surjective_of_injective (f := shift.toLinearMap) hinj
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hinj, hsurj⟩

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
  have hshiftUnit := finiteCutoffContinuumBornDysonShiftOperator_isUnit
    side v m px py probeEnergy broadening disorderStrength hbar pMax
    hbroadening hdisorder hpMax
  have hoperatorUnit : IsUnit (matrixOperator M) := by
    rw [← finiteCutoffContinuumBornDysonShiftOperator_eq_matrix
      side v m px py probeEnergy broadening disorderStrength hbar pMax hbroadening]
    exact hshiftUnit
  let φ : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert) := Matrix.toEuclideanCLM
  have hmatrixUnit : IsUnit M := by
    apply (isUnit_map_iff φ M).mp
    simpa [φ, matrixOperator] using hoperatorUnit
  have hdetUnit : IsUnit M.det :=
    (Matrix.isUnit_iff_isUnit_det M).mp hmatrixUnit
  have hdet : M.det ≠ 0 := isUnit_iff_ne_zero.mp hdetUnit
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    simpa [pow_two] using Complex.I_mul_I
  have hdetEq :
      M.det = finiteCutoffContinuumBornDysonDenominator
        side v m px py probeEnergy broadening disorderStrength hbar pMax := by
    dsimp [M]
    rw [Matrix.det_fin_two]
    simp [finiteCutoffContinuumBornDysonShiftMatrix,
      finiteCutoffContinuumBornDysonDenominator, sigmaX, sigmaY, sigmaZ]
    ring_nf
    rw [hI]
    ring
  rw [hdetEq] at hdet
  exact hdet

end

end AnomalousHall.MassiveDirac
