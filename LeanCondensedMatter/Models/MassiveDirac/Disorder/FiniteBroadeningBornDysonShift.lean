import LeanCondensedMatter.Models.MassiveDirac.Disorder.FiniteBroadeningBornPropagator
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Born-Dyson shift and propagator inverse identities

The finite-cutoff Born-Dyson shift is the operator `G₀⁻¹ - Σ`, with the
Pauli-matrix realization determined by the same effective energy and mass
as the upstream `FiniteBroadeningBornPropagator`.

This module proves the matrix and bounded-operator inverse identities when the
quadratic Green denominator is nonzero, together with spectral-side adjoint
relations. The separate `FiniteBroadeningBornInvertibility` module derives
denominator nonvanishing from the dissipativity of the Born self-energy; those
analytic hypotheses are not prerequisites for defining the propagator itself.

No vanishing-broadening, weak-disorder, or conductivity limit is taken.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Matrix whose inverse is represented by `finiteCutoffContinuumBornDysonGreenMatrix`: the exact
finite-cutoff Born-Dyson shift `(z_s - Σ₀)I - vpₓσₓ - vpᵧσᵧ - (m + Σ_z)σ_z`. -/
noncomputable def finiteCutoffContinuumBornDysonShiftMatrix
    (side : SpectralSide)
    (v m px py probeEnergy broadening disorderStrength hbar pMax : ℝ) : Matrix2 :=
  finiteCutoffContinuumBornEffectiveEnergy
      side v m probeEnergy broadening disorderStrength hbar pMax • (1 : Matrix2) -
    (((v * px : ℝ) : ℂ)) • sigmaX -
    (((v * py : ℝ) : ℂ)) • sigmaY -
    finiteCutoffContinuumBornEffectiveMass
      side v m probeEnergy broadening disorderStrength hbar pMax • sigmaZ

private theorem finiteCutoffContinuumBornDysonShiftMatrix_det
    (side : SpectralSide)
    (v m px py probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    (finiteCutoffContinuumBornDysonShiftMatrix
      side v m px py probeEnergy broadening disorderStrength hbar pMax).det =
      finiteCutoffContinuumBornDysonDenominator
        side v m px py probeEnergy broadening disorderStrength hbar pMax := by
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    simpa [pow_two] using Complex.I_mul_I
  rw [Matrix.det_fin_two]
  simp [finiteCutoffContinuumBornDysonShiftMatrix,
    finiteCutoffContinuumBornDysonDenominator, sigmaX, sigmaY, sigmaZ,
    InternalSpace.pauliX, InternalSpace.pauliY, InternalSpace.pauliZ]
  ring_nf
  rw [hI]
  ring

/-- The explicit Pauli candidate is a right inverse of the finite-`η` Born-Dyson shift whenever its
quadratic denominator is nonzero. -/
theorem finiteCutoffContinuumBornDysonShiftMatrix_mul_greenMatrix
    (side : SpectralSide)
    (v m px py probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hden : finiteCutoffContinuumBornDysonDenominator
      side v m px py probeEnergy broadening disorderStrength hbar pMax ≠ 0) :
    finiteCutoffContinuumBornDysonShiftMatrix
        side v m px py probeEnergy broadening disorderStrength hbar pMax *
      finiteCutoffContinuumBornDysonGreenMatrix
        side v m px py probeEnergy broadening disorderStrength hbar pMax = 1 := by
  have hdenEq :
      finiteCutoffContinuumBornEffectiveEnergy
            side v m probeEnergy broadening disorderStrength hbar pMax ^ 2 -
          (((v * px : ℝ) : ℂ)) ^ 2 - (((v * py : ℝ) : ℂ)) ^ 2 -
          finiteCutoffContinuumBornEffectiveMass
            side v m probeEnergy broadening disorderStrength hbar pMax ^ 2 =
        finiteCutoffContinuumBornDysonDenominator
          side v m px py probeEnergy broadening disorderStrength hbar pMax := by
    unfold finiteCutoffContinuumBornDysonDenominator
    push_cast
    ring
  have hcoreDen :
      finiteCutoffContinuumBornEffectiveEnergy
            side v m probeEnergy broadening disorderStrength hbar pMax ^ 2 -
          (((v * px : ℝ) : ℂ)) ^ 2 - (((v * py : ℝ) : ℂ)) ^ 2 -
          finiteCutoffContinuumBornEffectiveMass
            side v m probeEnergy broadening disorderStrength hbar pMax ^ 2 ≠ 0 := by
    rw [hdenEq]
    exact hden
  have hgreen :
      finiteCutoffContinuumBornDysonGreenMatrix
          side v m px py probeEnergy broadening disorderStrength hbar pMax =
        (finiteCutoffContinuumBornDysonDenominator
          side v m px py probeEnergy broadening disorderStrength hbar pMax)⁻¹ •
          (finiteCutoffContinuumBornEffectiveEnergy
              side v m probeEnergy broadening disorderStrength hbar pMax • (1 : Matrix2) +
            (((v * px : ℝ) : ℂ)) • sigmaX +
            (((v * py : ℝ) : ℂ)) • sigmaY +
            finiteCutoffContinuumBornEffectiveMass
              side v m probeEnergy broadening disorderStrength hbar pMax • sigmaZ) := by
    simp [finiteCutoffContinuumBornDysonGreenMatrix,
      finiteCutoffContinuumBornDysonScalarCoefficient,
      finiteCutoffContinuumBornDysonPauliCoefficient, InternalSpace.pauliAxisComponent,
      smul_add, smul_smul]
  have hshift :
      finiteCutoffContinuumBornDysonShiftMatrix
          side v m px py probeEnergy broadening disorderStrength hbar pMax =
        finiteCutoffContinuumBornEffectiveEnergy
            side v m probeEnergy broadening disorderStrength hbar pMax • (1 : Matrix2) -
          ((((v * px : ℝ) : ℂ)) • sigmaX +
            (((v * py : ℝ) : ℂ)) • sigmaY +
            finiteCutoffContinuumBornEffectiveMass
              side v m probeEnergy broadening disorderStrength hbar pMax • sigmaZ) := by
    unfold finiteCutoffContinuumBornDysonShiftMatrix
    module
  rw [hgreen, ← hdenEq, hshift]
  simpa [smul_add, smul_smul, add_assoc] using
    (InternalSpace.pauliShiftMatrix_mul_closedInverse
      (finiteCutoffContinuumBornEffectiveEnergy
        side v m probeEnergy broadening disorderStrength hbar pMax)
      (((v * px : ℝ) : ℂ)) (((v * py : ℝ) : ℂ))
      (finiteCutoffContinuumBornEffectiveMass
        side v m probeEnergy broadening disorderStrength hbar pMax)
      hcoreDen)

/-- Operator-level Dyson shift corresponding exactly to the existing finite-cutoff Born self-energy. -/
noncomputable def finiteCutoffContinuumBornDysonShiftOperator
    (side : SpectralSide)
    (v m px py probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  algebraMap ℂ (DiracHilbert →L[ℂ] DiracHilbert)
      (spectralParameter side probeEnergy broadening) -
    hamiltonianOperator v m px py -
    finiteCutoffContinuumBornSelfEnergy
      side v m probeEnergy broadening disorderStrength hbar pMax

/-- Adjointing the Born-Dyson shift exchanges the spectral side. -/
theorem star_finiteCutoffContinuumBornDysonShiftOperator
    (side : SpectralSide)
    (v m px py probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hbroadening : broadening ≠ 0) :
    star (finiteCutoffContinuumBornDysonShiftOperator
      side v m px py probeEnergy broadening disorderStrength hbar pMax) =
      finiteCutoffContinuumBornDysonShiftOperator
        side.opposite v m px py probeEnergy broadening disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornDysonShiftOperator
  rw [star_sub, star_sub, (hamiltonianOperator_isSelfAdjoint v m px py).star_eq]
  rw [star_finiteCutoffContinuumBornSelfEnergy
    side v m probeEnergy broadening disorderStrength hbar pMax hbroadening]
  simp [Algebra.algebraMap_eq_smul_one, spectralParameter]

/-- The operator Dyson shift is exactly the bounded realization of the explicit Pauli shift matrix. -/
theorem finiteCutoffContinuumBornDysonShiftOperator_eq_matrix
    (side : SpectralSide)
    (v m px py probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hbroadening : broadening ≠ 0) :
    finiteCutoffContinuumBornDysonShiftOperator
        side v m px py probeEnergy broadening disorderStrength hbar pMax =
      matrixOperator
        (finiteCutoffContinuumBornDysonShiftMatrix
          side v m px py probeEnergy broadening disorderStrength hbar pMax) := by
  rw [finiteCutoffContinuumBornDysonShiftOperator,
    finiteCutoffContinuumBornSelfEnergy_eq
      side v m probeEnergy broadening disorderStrength hbar pMax hbroadening,
    hamiltonianOperator_eq_pauli]
  have hmatrix :
      matrixOperator
          (finiteCutoffContinuumBornDysonShiftMatrix
            side v m px py probeEnergy broadening disorderStrength hbar pMax) =
        finiteCutoffContinuumBornEffectiveEnergy
            side v m probeEnergy broadening disorderStrength hbar pMax •
          (1 : DiracHilbert →L[ℂ] DiracHilbert) -
        (((v * px : ℝ) : ℂ)) • matrixOperator sigmaX -
        (((v * py : ℝ) : ℂ)) • matrixOperator sigmaY -
        finiteCutoffContinuumBornEffectiveMass
            side v m probeEnergy broadening disorderStrength hbar pMax •
          matrixOperator sigmaZ := by
    unfold finiteCutoffContinuumBornDysonShiftMatrix matrixOperator
    simp only [map_sub, map_smul, map_one]
  rw [hmatrix]
  unfold finiteCutoffContinuumBornEffectiveEnergy finiteCutoffContinuumBornEffectiveMass
  simp [Algebra.algebraMap_eq_smul_one]
  module

private theorem star_finiteCutoffContinuumBornDysonShiftMatrix
    (side : SpectralSide)
    (v m px py probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hbroadening : broadening ≠ 0) :
    star (finiteCutoffContinuumBornDysonShiftMatrix
      side v m px py probeEnergy broadening disorderStrength hbar pMax) =
      finiteCutoffContinuumBornDysonShiftMatrix
        side.opposite v m px py probeEnergy broadening disorderStrength hbar pMax := by
  let φ : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert) := Matrix.toEuclideanCLM
  have hstar := star_finiteCutoffContinuumBornDysonShiftOperator
    side v m px py probeEnergy broadening disorderStrength hbar pMax hbroadening
  rw [finiteCutoffContinuumBornDysonShiftOperator_eq_matrix
        side v m px py probeEnergy broadening disorderStrength hbar pMax hbroadening,
      finiteCutoffContinuumBornDysonShiftOperator_eq_matrix
        side.opposite v m px py probeEnergy broadening disorderStrength hbar pMax hbroadening] at hstar
  change star (φ.toFun (finiteCutoffContinuumBornDysonShiftMatrix
      side v m px py probeEnergy broadening disorderStrength hbar pMax)) =
    φ.toFun (finiteCutoffContinuumBornDysonShiftMatrix
      side.opposite v m px py probeEnergy broadening disorderStrength hbar pMax) at hstar
  apply φ.injective
  change φ.toFun (star (finiteCutoffContinuumBornDysonShiftMatrix
      side v m px py probeEnergy broadening disorderStrength hbar pMax)) =
    φ.toFun (finiteCutoffContinuumBornDysonShiftMatrix
      side.opposite v m px py probeEnergy broadening disorderStrength hbar pMax)
  exact (φ.map_star' _).trans hstar

private theorem star_finiteCutoffContinuumBornDysonDenominator
    (side : SpectralSide)
    (v m px py probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hbroadening : broadening ≠ 0) :
    star (finiteCutoffContinuumBornDysonDenominator
      side v m px py probeEnergy broadening disorderStrength hbar pMax) =
      finiteCutoffContinuumBornDysonDenominator
        side.opposite v m px py probeEnergy broadening disorderStrength hbar pMax := by
  calc
    star (finiteCutoffContinuumBornDysonDenominator
        side v m px py probeEnergy broadening disorderStrength hbar pMax) =
        star ((finiteCutoffContinuumBornDysonShiftMatrix
          side v m px py probeEnergy broadening disorderStrength hbar pMax).det) := by
      rw [finiteCutoffContinuumBornDysonShiftMatrix_det]
    _ = (star (finiteCutoffContinuumBornDysonShiftMatrix
          side v m px py probeEnergy broadening disorderStrength hbar pMax)).det := by
      rw [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose]
    _ = (finiteCutoffContinuumBornDysonShiftMatrix
          side.opposite v m px py probeEnergy broadening disorderStrength hbar pMax).det := by
      rw [star_finiteCutoffContinuumBornDysonShiftMatrix
        side v m px py probeEnergy broadening disorderStrength hbar pMax hbroadening]
    _ = finiteCutoffContinuumBornDysonDenominator
        side.opposite v m px py probeEnergy broadening disorderStrength hbar pMax := by
      rw [finiteCutoffContinuumBornDysonShiftMatrix_det]

/-- At nonzero external broadening and nonzero Born-Dyson denominator, the explicit propagator
candidate is a right inverse of the full finite-`η` Born-Dyson shift. -/
theorem finiteCutoffContinuumBornDysonShiftOperator_mul_greenOperator
    (side : SpectralSide)
    (v m px py probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hbroadening : broadening ≠ 0)
    (hden : finiteCutoffContinuumBornDysonDenominator
      side v m px py probeEnergy broadening disorderStrength hbar pMax ≠ 0) :
    finiteCutoffContinuumBornDysonShiftOperator
        side v m px py probeEnergy broadening disorderStrength hbar pMax *
      finiteCutoffContinuumBornDysonGreenOperator
        side v m px py probeEnergy broadening disorderStrength hbar pMax = 1 := by
  rw [finiteCutoffContinuumBornDysonShiftOperator_eq_matrix
    side v m px py probeEnergy broadening disorderStrength hbar pMax hbroadening]
  unfold finiteCutoffContinuumBornDysonGreenOperator
  let φ : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert) := Matrix.toEuclideanCLM
  change φ (finiteCutoffContinuumBornDysonShiftMatrix
      side v m px py probeEnergy broadening disorderStrength hbar pMax) *
    φ (finiteCutoffContinuumBornDysonGreenMatrix
      side v m px py probeEnergy broadening disorderStrength hbar pMax) = 1
  rw [← map_mul,
    finiteCutoffContinuumBornDysonShiftMatrix_mul_greenMatrix
      side v m px py probeEnergy broadening disorderStrength hbar pMax hden,
    map_one]

/-- Under nonzero broadening and a nonzero Born-Dyson denominator, adjointing the finite-`η`
Born-Dyson propagator exchanges the spectral side. -/
theorem star_finiteCutoffContinuumBornDysonGreenOperator
    (side : SpectralSide)
    (v m px py probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hbroadening : broadening ≠ 0)
    (hden : finiteCutoffContinuumBornDysonDenominator
      side v m px py probeEnergy broadening disorderStrength hbar pMax ≠ 0) :
    star (finiteCutoffContinuumBornDysonGreenOperator
      side v m px py probeEnergy broadening disorderStrength hbar pMax) =
      finiteCutoffContinuumBornDysonGreenOperator
        side.opposite v m px py probeEnergy broadening disorderStrength hbar pMax := by
  have hdenOpposite : finiteCutoffContinuumBornDysonDenominator
      side.opposite v m px py probeEnergy broadening disorderStrength hbar pMax ≠ 0 := by
    rw [← star_finiteCutoffContinuumBornDysonDenominator
      side v m px py probeEnergy broadening disorderStrength hbar pMax hbroadening]
    exact star_ne_zero.mpr hden
  have hside := finiteCutoffContinuumBornDysonShiftOperator_mul_greenOperator
    side v m px py probeEnergy broadening disorderStrength hbar pMax hbroadening hden
  have hopposite := finiteCutoffContinuumBornDysonShiftOperator_mul_greenOperator
    side.opposite v m px py probeEnergy broadening disorderStrength hbar pMax
      hbroadening hdenOpposite
  have hleft :
      star (finiteCutoffContinuumBornDysonGreenOperator
          side v m px py probeEnergy broadening disorderStrength hbar pMax) *
        finiteCutoffContinuumBornDysonShiftOperator
          side.opposite v m px py probeEnergy broadening disorderStrength hbar pMax = 1 := by
    have hstar := congrArg star hside
    rw [star_mul,
      star_finiteCutoffContinuumBornDysonShiftOperator
        side v m px py probeEnergy broadening disorderStrength hbar pMax hbroadening,
      star_one] at hstar
    exact hstar
  calc
    star (finiteCutoffContinuumBornDysonGreenOperator
        side v m px py probeEnergy broadening disorderStrength hbar pMax) =
        star (finiteCutoffContinuumBornDysonGreenOperator
          side v m px py probeEnergy broadening disorderStrength hbar pMax) * 1 := by
      simp
    _ = star (finiteCutoffContinuumBornDysonGreenOperator
          side v m px py probeEnergy broadening disorderStrength hbar pMax) *
        (finiteCutoffContinuumBornDysonShiftOperator
            side.opposite v m px py probeEnergy broadening disorderStrength hbar pMax *
          finiteCutoffContinuumBornDysonGreenOperator
            side.opposite v m px py probeEnergy broadening disorderStrength hbar pMax) := by
      rw [hopposite]
    _ = (star (finiteCutoffContinuumBornDysonGreenOperator
            side v m px py probeEnergy broadening disorderStrength hbar pMax) *
          finiteCutoffContinuumBornDysonShiftOperator
            side.opposite v m px py probeEnergy broadening disorderStrength hbar pMax) *
        finiteCutoffContinuumBornDysonGreenOperator
          side.opposite v m px py probeEnergy broadening disorderStrength hbar pMax := by
      rw [mul_assoc]
    _ = finiteCutoffContinuumBornDysonGreenOperator
        side.opposite v m px py probeEnergy broadening disorderStrength hbar pMax := by
      rw [hleft, one_mul]

end

end QuantumTheory.Models.MassiveDirac
