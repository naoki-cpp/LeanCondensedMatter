import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.ContinuumBorn
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Operator
import LeanCondensedMatter.Transport.Streda.RetardedAdvanced
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite-external-broadening Born-Dyson propagator

The continuum Born self-energy already exists at finite cutoff and finite external broadening as

```text
Σ_s(ε,η;Λ) = Σ₀,s I + Σ_z,s σ_z.
```

This module puts those existing coefficients back into the massive-Dirac Dyson shift without first
taking `η → 0⁺`.  For either spectral side,

```text
ε̃_s = z_s(ε,η) - Σ₀,s,
m̃_s = m + Σ_z,s,
D_s(p) = ε̃_s² - m̃_s² - v²(pₓ²+pᵧ²),
G_B,s = D_s⁻¹ (ε̃_s I + v pₓ σₓ + v pᵧ σᵧ + m̃_s σ_z).
```

The sign `m̃_s = m + Σ_z,s` follows from
`G₀⁻¹ - Σ = (z_s - Σ₀) I - v p·σ - (m + Σ_z) σ_z`.

This is a finite-cutoff Born-Dyson approximation candidate.  It is not identified with the exact
disorder average, and no `η → 0⁺`, weak-disorder, SCBA/Ward, or conductivity-limit statement is made
here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Scalar Pauli coefficient of the existing finite-cutoff continuum Born self-energy. -/
noncomputable def finiteCutoffContinuumBornScalarSelfEnergyCoefficient
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  (((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ) *
    finiteCutoffContinuumBornScalarIntegral
      side v m probeEnergy broadening pMax)

/-- `σ_z` Pauli coefficient of the existing finite-cutoff continuum Born self-energy. -/
noncomputable def finiteCutoffContinuumBornZSelfEnergyCoefficient
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  (((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ) *
    finiteCutoffContinuumBornZIntegral
      side v m probeEnergy broadening pMax)

/-- Named coefficient form of the existing finite-cutoff continuum Born self-energy. -/
theorem finiteCutoffContinuumBornSelfEnergy_eq_coefficients
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hbroadening : broadening ≠ 0) :
    finiteCutoffContinuumBornSelfEnergy
        side v m probeEnergy broadening disorderStrength hbar pMax =
      finiteCutoffContinuumBornScalarSelfEnergyCoefficient
          side v m probeEnergy broadening disorderStrength hbar pMax • 1 +
        finiteCutoffContinuumBornZSelfEnergyCoefficient
          side v m probeEnergy broadening disorderStrength hbar pMax • matrixOperator sigmaZ := by
  simpa [finiteCutoffContinuumBornScalarSelfEnergyCoefficient,
    finiteCutoffContinuumBornZSelfEnergyCoefficient] using
    finiteCutoffContinuumBornSelfEnergy_eq
      side v m probeEnergy broadening disorderStrength hbar pMax hbroadening

@[simp] theorem finiteCutoffContinuumBornScalarSelfEnergyCoefficient_zero_disorder
    (side : SpectralSide) (v m probeEnergy broadening hbar pMax : ℝ) :
    finiteCutoffContinuumBornScalarSelfEnergyCoefficient
      side v m probeEnergy broadening 0 hbar pMax = 0 := by
  simp [finiteCutoffContinuumBornScalarSelfEnergyCoefficient]

@[simp] theorem finiteCutoffContinuumBornZSelfEnergyCoefficient_zero_disorder
    (side : SpectralSide) (v m probeEnergy broadening hbar pMax : ℝ) :
    finiteCutoffContinuumBornZSelfEnergyCoefficient
      side v m probeEnergy broadening 0 hbar pMax = 0 := by
  simp [finiteCutoffContinuumBornZSelfEnergyCoefficient]

/-- Finite-`η` Born-Dyson effective spectral energy `z_s - Σ₀,s`. -/
noncomputable def finiteCutoffContinuumBornEffectiveEnergy
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  spectralParameter side probeEnergy broadening -
    finiteCutoffContinuumBornScalarSelfEnergyCoefficient
      side v m probeEnergy broadening disorderStrength hbar pMax

/-- Finite-`η` Born-Dyson effective Dirac mass `m + Σ_z,s`. -/
noncomputable def finiteCutoffContinuumBornEffectiveMass
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  (m : ℂ) + finiteCutoffContinuumBornZSelfEnergyCoefficient
    side v m probeEnergy broadening disorderStrength hbar pMax

/-- Quadratic denominator of the finite-`η` Born-Dyson massive-Dirac propagator candidate. -/
noncomputable def finiteCutoffContinuumBornDysonDenominator
    (side : SpectralSide)
    (v m px py probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  finiteCutoffContinuumBornEffectiveEnergy
      side v m probeEnergy broadening disorderStrength hbar pMax ^ 2 -
    finiteCutoffContinuumBornEffectiveMass
      side v m probeEnergy broadening disorderStrength hbar pMax ^ 2 -
    ((v ^ 2 * (px ^ 2 + py ^ 2) : ℝ) : ℂ)

/-- Scalar Pauli coefficient of the finite-`η` Born-Dyson propagator candidate. -/
noncomputable def finiteCutoffContinuumBornDysonScalarCoefficient
    (side : SpectralSide)
    (v m px py probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  (finiteCutoffContinuumBornDysonDenominator
      side v m px py probeEnergy broadening disorderStrength hbar pMax)⁻¹ *
    finiteCutoffContinuumBornEffectiveEnergy
      side v m probeEnergy broadening disorderStrength hbar pMax

/-- `σₓ` Pauli coefficient of the finite-`η` Born-Dyson propagator candidate. -/
noncomputable def finiteCutoffContinuumBornDysonXCoefficient
    (side : SpectralSide)
    (v m px py probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  (finiteCutoffContinuumBornDysonDenominator
      side v m px py probeEnergy broadening disorderStrength hbar pMax)⁻¹ *
    ((v * px : ℝ) : ℂ)

/-- `σᵧ` Pauli coefficient of the finite-`η` Born-Dyson propagator candidate. -/
noncomputable def finiteCutoffContinuumBornDysonYCoefficient
    (side : SpectralSide)
    (v m px py probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  (finiteCutoffContinuumBornDysonDenominator
      side v m px py probeEnergy broadening disorderStrength hbar pMax)⁻¹ *
    ((v * py : ℝ) : ℂ)

/-- `σ_z` Pauli coefficient of the finite-`η` Born-Dyson propagator candidate. -/
noncomputable def finiteCutoffContinuumBornDysonZCoefficient
    (side : SpectralSide)
    (v m px py probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  (finiteCutoffContinuumBornDysonDenominator
      side v m px py probeEnergy broadening disorderStrength hbar pMax)⁻¹ *
    finiteCutoffContinuumBornEffectiveMass
      side v m probeEnergy broadening disorderStrength hbar pMax

/-- Matrix form of the finite-`η` Born-Dyson propagator candidate. -/
noncomputable def finiteCutoffContinuumBornDysonGreenMatrix
    (side : SpectralSide)
    (v m px py probeEnergy broadening disorderStrength hbar pMax : ℝ) : Matrix2 :=
  finiteCutoffContinuumBornDysonScalarCoefficient
      side v m px py probeEnergy broadening disorderStrength hbar pMax • (1 : Matrix2) +
    finiteCutoffContinuumBornDysonXCoefficient
      side v m px py probeEnergy broadening disorderStrength hbar pMax • sigmaX +
    finiteCutoffContinuumBornDysonYCoefficient
      side v m px py probeEnergy broadening disorderStrength hbar pMax • sigmaY +
    finiteCutoffContinuumBornDysonZCoefficient
      side v m px py probeEnergy broadening disorderStrength hbar pMax • sigmaZ

/-- Bounded-operator form of the finite-`η` Born-Dyson propagator candidate. -/
noncomputable def finiteCutoffContinuumBornDysonGreenOperator
    (side : SpectralSide)
    (v m px py probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  matrixOperator
    (finiteCutoffContinuumBornDysonGreenMatrix
      side v m px py probeEnergy broadening disorderStrength hbar pMax)

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
    finiteCutoffContinuumBornDysonDenominator, sigmaX, sigmaY, sigmaZ]
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
  have hunit : IsUnit (finiteCutoffContinuumBornDysonShiftMatrix
      side v m px py probeEnergy broadening disorderStrength hbar pMax).det := by
    rw [finiteCutoffContinuumBornDysonShiftMatrix_det]
    exact isUnit_iff_ne_zero.mpr hden
  rw [show finiteCutoffContinuumBornDysonGreenMatrix
      side v m px py probeEnergy broadening disorderStrength hbar pMax =
      (finiteCutoffContinuumBornDysonShiftMatrix
        side v m px py probeEnergy broadening disorderStrength hbar pMax)⁻¹ by
    rw [Matrix.inv_def, Ring.inverse_eq_inv, finiteCutoffContinuumBornDysonShiftMatrix_det]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [finiteCutoffContinuumBornDysonShiftMatrix,
        finiteCutoffContinuumBornDysonGreenMatrix,
        finiteCutoffContinuumBornDysonScalarCoefficient,
        finiteCutoffContinuumBornDysonXCoefficient,
        finiteCutoffContinuumBornDysonYCoefficient,
        finiteCutoffContinuumBornDysonZCoefficient,
        Matrix.adjugate_fin_two, sigmaX, sigmaY, sigmaZ] <;>
      ring]
  exact Matrix.mul_nonsing_inv _ hunit

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
    finiteCutoffContinuumBornSelfEnergy_eq_coefficients
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

/-- At zero disorder strength the finite-`η` Born-Dyson denominator reduces to the clean Pauli Green
denominator. -/
@[simp] theorem finiteCutoffContinuumBornDysonDenominator_zero_disorder
    (side : SpectralSide)
    (v m px py probeEnergy broadening hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonDenominator
        side v m px py probeEnergy broadening 0 hbar pMax =
      pauliGreenDenominator side v m px py probeEnergy broadening := by
  unfold pauliGreenDenominator
  simp [finiteCutoffContinuumBornDysonDenominator,
    finiteCutoffContinuumBornEffectiveEnergy,
    finiteCutoffContinuumBornEffectiveMass,
    pauliGreenDenominatorOfRegulator, spectralParameter, energySq]
  ring

/-- At zero disorder strength the finite-`η` Born-Dyson propagator candidate is exactly the clean
massive-Dirac Pauli Green operator. -/
@[simp] theorem finiteCutoffContinuumBornDysonGreenOperator_zero_disorder
    (side : SpectralSide)
    (v m px py probeEnergy broadening hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonGreenOperator
        side v m px py probeEnergy broadening 0 hbar pMax =
      pauliGreenOperator side v m px py probeEnergy broadening := by
  unfold finiteCutoffContinuumBornDysonGreenOperator
    finiteCutoffContinuumBornDysonGreenMatrix
    finiteCutoffContinuumBornDysonScalarCoefficient
    finiteCutoffContinuumBornDysonXCoefficient
    finiteCutoffContinuumBornDysonYCoefficient
    finiteCutoffContinuumBornDysonZCoefficient
    pauliGreenOperator pauliGreenOperatorOfRegulator
    pauliGreenScalarCoefficientOfRegulator pauliGreenXCoefficientOfRegulator
    pauliGreenYCoefficientOfRegulator pauliGreenZCoefficientOfRegulator
    pauliGreenDenominatorOfRegulator
  simp [finiteCutoffContinuumBornEffectiveEnergy,
    finiteCutoffContinuumBornEffectiveMass, spectralParameter,
    pauliGreenDenominator, pauliGreenDenominatorOfRegulator,
    matrixOperator, map_add, map_smul]

/-- Pointwise longitudinal RA trace channel with finite external broadening retained in both
Born-Dyson Green operators and an arbitrary supplied source/dressed vertex. -/
noncomputable def finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedTraceKernel
    (e v m px py probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (dressedVertex : DiracHilbert →L[ℂ] DiracHilbert) : ℂ :=
  retardedAdvancedVertexTraceKernel
    (currentOperator .x e v)
    (finiteCutoffContinuumBornDysonGreenOperator
      .retarded v m px py probeEnergy broadening disorderStrength hbar pMax)
    dressedVertex
    (finiteCutoffContinuumBornDysonGreenOperator
      .advanced v m px py probeEnergy broadening disorderStrength hbar pMax)

/-- The finite-`η` Born-Dyson RA channel reduces exactly to the clean supplied-Green RA channel when
the disorder strength is zero. -/
@[simp] theorem finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedTraceKernel_zero_disorder
    (e v m px py probeEnergy broadening hbar pMax : ℝ)
    (dressedVertex : DiracHilbert →L[ℂ] DiracHilbert) :
    finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedTraceKernel
        e v m px py probeEnergy broadening 0 hbar pMax dressedVertex =
      retardedAdvancedVertexTraceKernel
        (currentOperator .x e v)
        (pauliGreenOperator .retarded v m px py probeEnergy broadening)
        dressedVertex
        (pauliGreenOperator .advanced v m px py probeEnergy broadening) := by
  simp [finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedTraceKernel]

end

end MassiveDirac
end AnomalousHall
