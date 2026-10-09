import LeanCondensedMatter.Models.MassiveDirac.Disorder.TMatrix.ScalarImpurity
import LeanCondensedMatter.Transport.Analysis.ContinuumMeasure
import LeanCondensedMatter.Models.MassiveDirac.Disorder.FiniteBroadeningBornRealSpacePropagator

set_option linter.style.header false

/-!
# Finite-cutoff Born-Dyson loop for scalar-impurity T-matrices

The concrete loop evaluates the Born-Dyson real-space Green matrix at the spatial origin.
Its regulator, finite cutoff, and physical momentum measure belong to this realization.
The zero-disorder identity relates the loop to the clean radial Green integral; under
W = n_imp v_imp², its quadratic self-energy coefficient is the continuum Born self-energy.
The linear mean-potential term remains separate. The supplied-loop scalar-impurity construction
is specialized here without asserting a self-consistent T-matrix or exact disorder average.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Finite-cutoff Born-Dyson zero-field loop at the spatial origin. Each real-space Green block
already contains the physical momentum measure, so downstream T-matrix data must not attach it
again. -/
noncomputable def finiteCutoffContinuumBornDysonGreenLoopMatrix
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : Matrix2 :=
  finiteCutoffContinuumBornDysonRealSpaceGreenMatrix
    side v m probeEnergy broadening disorderStrength hbar pMax (polarPoint2D 0 0)

/-- The Born-Dyson loop is exactly the existing radial physical-momentum integral at radius zero.
This theorem exposes the cutoff and the single momentum-measure prefactor directly in the T-matrix
API. -/
theorem finiteCutoffContinuumBornDysonGreenLoopMatrix_apply_eq_radial_integral
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (i j : Fin 2) :
    finiteCutoffContinuumBornDysonGreenLoopMatrix
        side v m probeEnergy broadening disorderStrength hbar pMax i j =
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          finiteCutoffContinuumBornDysonRadialGreenEntryKernel
            side v m probeEnergy broadening disorderStrength hbar pMax 0 p i j := by
  rw [finiteCutoffContinuumBornDysonGreenLoopMatrix,
    finiteCutoffContinuumBornDysonRealSpaceGreenMatrix_radialAxis_eq]
  exact
    finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix_apply_eq_entryKernel_integral
      side v m probeEnergy broadening disorderStrength hbar pMax 0 i j

private theorem polarFourierZerothAngularKernel_zero :
    polarFourierZerothAngularKernel 0 = ((2 * Real.pi : ℝ) : ℂ) := by
  simp [polarFourierZerothAngularKernel, polarFourierRadialPhase]

private theorem polarFourierFirstCosineAngularKernel_zero :
    polarFourierFirstCosineAngularKernel 0 = 0 := by
  have h := integral_cos_mul_complex (z := (1 : ℂ)) one_ne_zero (0 : ℝ) (2 * Real.pi)
  simpa [polarFourierFirstCosineAngularKernel, polarFourierRadialPhase] using h

private theorem finiteCutoffContinuumBornDysonScalarCoefficient_zero_disorder
    (side : SpectralSide)
    (v m px py probeEnergy broadening hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonScalarCoefficient
        side v m px py probeEnergy broadening 0 hbar pMax =
      pauliGreenScalarCoefficient side v m px py probeEnergy broadening := by
  unfold finiteCutoffContinuumBornDysonScalarCoefficient
    finiteCutoffContinuumBornEffectiveEnergy
    pauliGreenScalarCoefficient pauliGreenScalarCoefficientOfRegulator
  rw [finiteCutoffContinuumBornDysonDenominator_zero_disorder]
  simp [finiteCutoffContinuumBornSelfEnergyCoefficient_zero_disorder,
    pauliGreenDenominator, spectralParameter]

private theorem finiteCutoffContinuumBornDysonPauliCoefficient_z_zero_disorder
    (side : SpectralSide)
    (v m px py probeEnergy broadening hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonPauliCoefficient
        .z side v m px py probeEnergy broadening 0 hbar pMax =
      pauliGreenPauliCoefficient .z side v m px py probeEnergy broadening := by
  unfold finiteCutoffContinuumBornDysonPauliCoefficient
    finiteCutoffContinuumBornEffectiveMass
    pauliGreenPauliCoefficient pauliGreenPauliCoefficientOfRegulator
  rw [finiteCutoffContinuumBornDysonDenominator_zero_disorder]
  simp [finiteCutoffContinuumBornSelfEnergyCoefficient_zero_disorder,
    pauliGreenDenominator, InternalSpace.pauliAxisComponent]

private theorem finiteCutoffContinuumBornDysonRadialGreenEntryKernel_zero_disorder_zero_radius
    (side : SpectralSide)
    (v m probeEnergy broadening hbar pMax p : ℝ) (i j : Fin 2) :
    finiteCutoffContinuumBornDysonRadialGreenEntryKernel
        side v m probeEnergy broadening 0 hbar pMax 0 p i j =
      ((2 * Real.pi : ℝ) : ℂ) *
        ((continuumBornRadialIntegrandOfRegulator
              .scalar v m probeEnergy (side.regulator broadening) p • (1 : Matrix2) +
            continuumBornRadialIntegrandOfRegulator
              .z v m probeEnergy (side.regulator broadening) p • sigmaZ) i j) := by
  fin_cases i <;> fin_cases j <;>
    simp [finiteCutoffContinuumBornDysonRadialGreenEntryKernel,
      polarFourierZerothAngularKernel_zero, polarFourierFirstCosineAngularKernel_zero,
      finiteCutoffContinuumBornDysonScalarCoefficient_zero_disorder,
      finiteCutoffContinuumBornDysonPauliCoefficient_z_zero_disorder,
      continuumBornRadialIntegrandOfRegulator,
      pauliGreenScalarCoefficient, pauliGreenPauliCoefficient,
      InternalSpace.pauliZ] <;>
    ring

private theorem finiteCutoffContinuumBornDysonGreenLoopMatrix_zero_disorder_eq_channels
    (side : SpectralSide)
    (v m probeEnergy broadening hbar pMax : ℝ)
    (hbroadening : broadening ≠ 0) :
    finiteCutoffContinuumBornDysonGreenLoopMatrix
        side v m probeEnergy broadening 0 hbar pMax =
      (((fullAngleMomentumMeasurePrefactor hbar : ℝ) : ℂ) *
          finiteCutoffContinuumBornIntegralOfRegulator
            .scalar v m probeEnergy (side.regulator broadening) pMax) • (1 : Matrix2) +
        (((fullAngleMomentumMeasurePrefactor hbar : ℝ) : ℂ) *
          finiteCutoffContinuumBornIntegralOfRegulator
            .z v m probeEnergy (side.regulator broadening) pMax) • sigmaZ := by
  have hregulator : side.regulator broadening ≠ 0 :=
    side.regulator_ne_zero hbroadening
  have hscalar :
      IntervalIntegrable
        (continuumBornRadialIntegrandOfRegulator
          .scalar v m probeEnergy (side.regulator broadening))
        MeasureTheory.volume 0 pMax :=
    (continuous_continuumBornRadialIntegrandOfRegulator
      .scalar v m probeEnergy (side.regulator broadening) hregulator).intervalIntegrable 0 pMax
  have hz :
      IntervalIntegrable
        (continuumBornRadialIntegrandOfRegulator
          .z v m probeEnergy (side.regulator broadening))
        MeasureTheory.volume 0 pMax :=
    (continuous_continuumBornRadialIntegrandOfRegulator
      .z v m probeEnergy (side.regulator broadening) hregulator).intervalIntegrable 0 pMax
  funext i j
  fin_cases i <;> fin_cases j
  · have hsigmaZ : sigmaZ 0 0 = 1 := rfl
    simp only [Matrix.add_apply, Matrix.smul_apply]
    simp only [Fin.zero_eta, Fin.isValue, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    rw [hsigmaZ]
    rw [finiteCutoffContinuumBornDysonGreenLoopMatrix_apply_eq_radial_integral]
    have hkernel (p : ℝ) :
        finiteCutoffContinuumBornDysonRadialGreenEntryKernel
            side v m probeEnergy broadening 0 hbar pMax 0 p 0 0 =
          ((2 * Real.pi : ℝ) : ℂ) *
            (continuumBornRadialIntegrandOfRegulator
                .scalar v m probeEnergy (side.regulator broadening) p +
              continuumBornRadialIntegrandOfRegulator
                .z v m probeEnergy (side.regulator broadening) p) := by
      simpa [InternalSpace.pauliZ] using
        finiteCutoffContinuumBornDysonRadialGreenEntryKernel_zero_disorder_zero_radius
          side v m probeEnergy broadening hbar pMax p 0 0
    simp_rw [hkernel]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add hscalar hz]
    unfold finiteCutoffContinuumBornIntegralOfRegulator fullAngleMomentumMeasurePrefactor
    push_cast
    ring
  · simp only [Matrix.add_apply, Matrix.smul_apply]
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, ne_eq, zero_ne_one, not_false_eq_true,
      Matrix.one_apply_ne, smul_eq_mul, mul_zero, zero_add, InternalSpace.pauliZ]
    rw [finiteCutoffContinuumBornDysonGreenLoopMatrix_apply_eq_radial_integral]
    have hkernel (p : ℝ) :
        finiteCutoffContinuumBornDysonRadialGreenEntryKernel
            side v m probeEnergy broadening 0 hbar pMax 0 p 0 1 = 0 := by
      simpa [InternalSpace.pauliZ] using
        finiteCutoffContinuumBornDysonRadialGreenEntryKernel_zero_disorder_zero_radius
          side v m probeEnergy broadening hbar pMax p 0 1
    simp_rw [hkernel]
    simp
  · simp only [Matrix.add_apply, Matrix.smul_apply]
    simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta, ne_eq, one_ne_zero, not_false_eq_true,
      Matrix.one_apply_ne, smul_eq_mul, mul_zero, zero_add, InternalSpace.pauliZ]
    rw [finiteCutoffContinuumBornDysonGreenLoopMatrix_apply_eq_radial_integral]
    have hkernel (p : ℝ) :
        finiteCutoffContinuumBornDysonRadialGreenEntryKernel
            side v m probeEnergy broadening 0 hbar pMax 0 p 1 0 = 0 := by
      simpa [InternalSpace.pauliZ] using
        finiteCutoffContinuumBornDysonRadialGreenEntryKernel_zero_disorder_zero_radius
          side v m probeEnergy broadening hbar pMax p 1 0
    simp_rw [hkernel]
    simp
  · have hsigmaZ : sigmaZ 1 1 = -1 := rfl
    simp only [Matrix.add_apply, Matrix.smul_apply]
    simp only [Fin.mk_one, Fin.isValue, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    rw [hsigmaZ]
    rw [finiteCutoffContinuumBornDysonGreenLoopMatrix_apply_eq_radial_integral]
    have hkernel (p : ℝ) :
        finiteCutoffContinuumBornDysonRadialGreenEntryKernel
            side v m probeEnergy broadening 0 hbar pMax 0 p 1 1 =
          ((2 * Real.pi : ℝ) : ℂ) *
            (continuumBornRadialIntegrandOfRegulator
                .scalar v m probeEnergy (side.regulator broadening) p -
              continuumBornRadialIntegrandOfRegulator
                .z v m probeEnergy (side.regulator broadening) p) := by
      simpa [InternalSpace.pauliZ, sub_eq_add_neg] using
        finiteCutoffContinuumBornDysonRadialGreenEntryKernel_zero_disorder_zero_radius
          side v m probeEnergy broadening hbar pMax p 1 1
    simp_rw [hkernel]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub hscalar hz]
    unfold finiteCutoffContinuumBornIntegralOfRegulator fullAngleMomentumMeasurePrefactor
    push_cast
    ring

/-- At zero Born disorder strength, the concrete T-matrix loop is exactly the canonical finite-cutoff
clean radial Green integral with the physical angular/momentum measure attached once. -/
theorem matrixOperator_finiteCutoffContinuumBornDysonGreenLoopMatrix_zero_disorder_eq
    (side : SpectralSide)
    (v m probeEnergy broadening hbar pMax : ℝ)
    (hbroadening : broadening ≠ 0) :
    matrixOperator
        (finiteCutoffContinuumBornDysonGreenLoopMatrix
          side v m probeEnergy broadening 0 hbar pMax) =
      (((fullAngleMomentumMeasurePrefactor hbar : ℝ) : ℂ)) •
        finiteCutoffContinuumBornGreenIntegralOfRegulator
          v m probeEnergy (side.regulator broadening) pMax := by
  rw [finiteCutoffContinuumBornDysonGreenLoopMatrix_zero_disorder_eq_channels
    side v m probeEnergy broadening hbar pMax hbroadening]
  rw [finiteCutoffContinuumBornGreenIntegralOfRegulator_eq
    v m probeEnergy (side.regulator broadening) pMax
    (side.regulator_ne_zero hbroadening)]
  simp only [matrixOperator, map_add, map_smul, map_one]
  module

/-- Under the explicit convention `W = n_imp v_imp²`, the quadratic clean-loop coefficient of
the scalar-impurity T-matrix self-energy is exactly the existing finite-cutoff continuum Born
self-energy. The linear mean-potential term `n_imp v_imp I` is not included in this identity. -/
theorem ScalarImpurityParameters.quadraticCleanLoopSelfEnergy_eq_finiteCutoffContinuumBornSelfEnergyOfRegulator
    (params : ScalarImpurityParameters)
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hbroadening : broadening ≠ 0)
    (hdisorder : disorderStrength = params.impurityDensity * params.impurityStrength ^ 2) :
    ((((params.impurityDensity * params.impurityStrength ^ 2 : ℝ) : ℂ))) •
        matrixOperator
          (finiteCutoffContinuumBornDysonGreenLoopMatrix
            side v m probeEnergy broadening 0 hbar pMax) =
      finiteCutoffContinuumBornSelfEnergyOfRegulator
        v m probeEnergy (side.regulator broadening) disorderStrength hbar pMax := by
  rw [matrixOperator_finiteCutoffContinuumBornDysonGreenLoopMatrix_zero_disorder_eq
    side v m probeEnergy broadening hbar pMax hbroadening]
  unfold finiteCutoffContinuumBornSelfEnergyOfRegulator
  rw [hdisorder]
  simp only [smul_smul]
  congr 1
  push_cast
  ring

/-- Born-Dyson approximation specialization of the scalar-impurity T-matrix. The supplied loop is
the explicit finite-cutoff finite-broadening Born-Dyson loop above, not a self-consistent T-matrix
closure. -/
noncomputable def finiteCutoffContinuumBornDysonScalarImpurityTMatrix
    (params : ScalarImpurityParameters)
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hinvertible :
      IsUnit
        (params.shiftMatrix
          (finiteCutoffContinuumBornDysonGreenLoopMatrix
            side v m probeEnergy broadening disorderStrength hbar pMax))) : Matrix2 :=
  params.tMatrix
    (finiteCutoffContinuumBornDysonGreenLoopMatrix
      side v m probeEnergy broadening disorderStrength hbar pMax)
    hinvertible

/-- Born-Dyson approximation specialization of the T-matrix self-energy. -/
noncomputable def finiteCutoffContinuumBornDysonScalarImpuritySelfEnergy
    (params : ScalarImpurityParameters)
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hinvertible :
      IsUnit
        (params.shiftMatrix
          (finiteCutoffContinuumBornDysonGreenLoopMatrix
            side v m probeEnergy broadening disorderStrength hbar pMax))) : Matrix2 :=
  params.selfEnergy
    (finiteCutoffContinuumBornDysonGreenLoopMatrix
      side v m probeEnergy broadening disorderStrength hbar pMax)
    hinvertible

end

end QuantumTheory.Models.MassiveDirac
