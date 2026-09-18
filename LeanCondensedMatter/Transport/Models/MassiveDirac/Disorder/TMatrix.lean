import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningBornRealSpacePropagator
import Mathlib.Algebra.Group.Units.Basic

set_option linter.style.header false

/-!
# Scalar-impurity T-matrix boundary for the massive-Dirac model

This module introduces the model-local algebraic boundary for a scalar-impurity T-matrix,

```text
T = v_imp * (1 - v_imp * G_loop)⁻¹,
Σ_T = n_imp * T.
```

This boundary follows the scalar-impurity construction in Onoda, Sugimoto, and Nagaosa,
*Phys. Rev. Lett.* **97**, 126602 (2006), Eqs. (12)–(15),
doi:10.1103/PhysRevLett.97.126602. The repository keeps the finite-cutoff loop and its regulator
explicit rather than importing the paper's numerical or self-consistency assumptions wholesale.

The supplied `greenLoop` is already a finite-cutoff, finite-regulator, zero-field dressed Green
loop and must already contain its physical momentum measure. The T-matrix layer does not reconstruct
that loop, attach a second momentum measure, or identify it with the clean propagator.

Invertibility is explicit through `IsUnit`. No geometric-series expansion, small-impurity limit,
self-consistent existence theorem, exact disorder-average identification, or skew-scattering
conductivity is asserted here. A concrete Born-Dyson supplied-loop constructor is exposed only as an
approximation boundary; it is not identified with the paper-faithful self-consistent T-matrix loop.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Finite-cutoff scalar-impurity T-matrix input. The dressed zero-field Green loop is supplied
explicitly together with the regulator/cutoff data whose provenance it represents. -/
structure ScalarImpurityTMatrixInput where
  /-- Impurity density `n_imp`, kept separate from the aggregate Born disorder strength. -/
  impurityDensity : ℝ
  /-- Scalar single-impurity potential strength `v_imp`. -/
  impurityStrength : ℝ
  /-- Nonzero signed spectral regulator carried by the supplied dressed Green loop. -/
  regulator : ℝ
  /-- Finite radial momentum cutoff carried by the supplied dressed Green loop. -/
  pMax : ℝ
  /-- Finite-cutoff dressed zero-field Green loop, including its physical momentum measure. -/
  greenLoop : Matrix2
  /-- The impurity density is positive. -/
  impurityDensity_pos : 0 < impurityDensity
  /-- The scalar impurity potential is nonzero. -/
  impurityStrength_ne_zero : impurityStrength ≠ 0
  /-- The signed spectral regulator is nonzero. -/
  regulator_ne_zero : regulator ≠ 0
  /-- The radial momentum cutoff is nonnegative. -/
  cutoff_nonneg : 0 ≤ pMax

/-- Matrix shifted by the scalar impurity loop, `1 - v_imp G_loop`. -/
def ScalarImpurityTMatrixInput.shiftMatrix
    (input : ScalarImpurityTMatrixInput) : Matrix2 :=
  1 - (((input.impurityStrength : ℝ) : ℂ)) • input.greenLoop

/-- Inverse of the T-matrix shift under an explicit unit hypothesis. -/
noncomputable def ScalarImpurityTMatrixInput.inverseShiftMatrix
    (input : ScalarImpurityTMatrixInput)
    (hinvertible : IsUnit input.shiftMatrix) : Matrix2 :=
  (↑(hinvertible.unit⁻¹) : Matrix2)

/-- Scalar-impurity T-matrix `T = v_imp (1 - v_imp G_loop)⁻¹`. -/
noncomputable def ScalarImpurityTMatrixInput.tMatrix
    (input : ScalarImpurityTMatrixInput)
    (hinvertible : IsUnit input.shiftMatrix) : Matrix2 :=
  (((input.impurityStrength : ℝ) : ℂ)) • input.inverseShiftMatrix hinvertible

/-- T-matrix self-energy `Σ_T = n_imp T`, with density and single-impurity strength kept distinct. -/
noncomputable def ScalarImpurityTMatrixInput.selfEnergy
    (input : ScalarImpurityTMatrixInput)
    (hinvertible : IsUnit input.shiftMatrix) : Matrix2 :=
  (((input.impurityDensity : ℝ) : ℂ)) • input.tMatrix hinvertible

/-- The explicit inverse is a right inverse of `1 - v_imp G_loop`. -/
theorem ScalarImpurityTMatrixInput.shiftMatrix_mul_inverseShiftMatrix
    (input : ScalarImpurityTMatrixInput)
    (hinvertible : IsUnit input.shiftMatrix) :
    input.shiftMatrix * input.inverseShiftMatrix hinvertible = 1 := by
  simpa [ScalarImpurityTMatrixInput.inverseShiftMatrix] using hinvertible.mul_val_inv

/-- The explicit inverse is also a left inverse of `1 - v_imp G_loop`. -/
theorem ScalarImpurityTMatrixInput.inverseShiftMatrix_mul_shiftMatrix
    (input : ScalarImpurityTMatrixInput)
    (hinvertible : IsUnit input.shiftMatrix) :
    input.inverseShiftMatrix hinvertible * input.shiftMatrix = 1 := by
  simpa [ScalarImpurityTMatrixInput.inverseShiftMatrix] using hinvertible.val_inv_mul

/-- Multiplying the T-matrix by its shift from the left gives the scalar impurity
potential. -/
theorem ScalarImpurityTMatrixInput.shiftMatrix_mul_tMatrix
    (input : ScalarImpurityTMatrixInput)
    (hinvertible : IsUnit input.shiftMatrix) :
    input.shiftMatrix * input.tMatrix hinvertible =
      (((input.impurityStrength : ℝ) : ℂ)) • (1 : Matrix2) := by
  unfold ScalarImpurityTMatrixInput.tMatrix
  rw [mul_smul_comm, input.shiftMatrix_mul_inverseShiftMatrix hinvertible]

/-- Multiplying the T-matrix by its shift from the right gives the same scalar impurity potential. -/
theorem ScalarImpurityTMatrixInput.tMatrix_mul_shiftMatrix
    (input : ScalarImpurityTMatrixInput)
    (hinvertible : IsUnit input.shiftMatrix) :
    input.tMatrix hinvertible * input.shiftMatrix =
      (((input.impurityStrength : ℝ) : ℂ)) • (1 : Matrix2) := by
  unfold ScalarImpurityTMatrixInput.tMatrix
  rw [smul_mul_assoc, input.inverseShiftMatrix_mul_shiftMatrix hinvertible]

/-- Exact Lippmann--Schwinger fixed-point identity. This follows from invertibility alone and does
not assert convergence of a geometric series. -/
theorem ScalarImpurityTMatrixInput.tMatrix_eq_bare_add_loop_tMatrix
    (input : ScalarImpurityTMatrixInput)
    (hinvertible : IsUnit input.shiftMatrix) :
    input.tMatrix hinvertible =
      (((input.impurityStrength : ℝ) : ℂ)) • (1 : Matrix2) +
        (((input.impurityStrength : ℝ) : ℂ)) •
          (input.greenLoop * input.tMatrix hinvertible) := by
  have h := input.shiftMatrix_mul_tMatrix hinvertible
  rw [ScalarImpurityTMatrixInput.shiftMatrix] at h
  simp only [sub_mul, one_mul, smul_mul_assoc] at h
  exact (sub_eq_iff_eq_add).mp h

/-- The self-energy keeps the impurity density as an external scalar multiplier of the T-matrix. -/
@[simp]
theorem ScalarImpurityTMatrixInput.selfEnergy_eq
    (input : ScalarImpurityTMatrixInput)
    (hinvertible : IsUnit input.shiftMatrix) :
    input.selfEnergy hinvertible =
      (((input.impurityDensity : ℝ) : ℂ)) • input.tMatrix hinvertible :=
  rfl

/-- Finite-cutoff Born-Dyson zero-field loop at the spatial origin. Each real-space Green block
already contains the physical momentum measure, so downstream T-matrix data must not attach it
again. -/
noncomputable def finiteCutoffContinuumBornDysonGreenLoopMatrix
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : Matrix2 :=
  finiteCutoffContinuumBornDysonRealSpaceGreenMatrix
    side v m probeEnergy broadening disorderStrength hbar pMax (polarPoint2D 0 0)

/-- Build scalar-impurity T-matrix input from the existing finite-cutoff Born-Dyson dressed loop.
This is an explicit approximation boundary, not a self-consistent T-matrix closure theorem. -/
noncomputable def finiteCutoffContinuumBornDysonScalarImpurityTMatrixInput
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax
      impurityDensity impurityStrength : ℝ)
    (hbroadening : broadening ≠ 0)
    (hcutoff : 0 ≤ pMax)
    (hdensity : 0 < impurityDensity)
    (hstrength : impurityStrength ≠ 0) :
    ScalarImpurityTMatrixInput where
  impurityDensity := impurityDensity
  impurityStrength := impurityStrength
  regulator := side.regulator broadening
  pMax := pMax
  greenLoop :=
    finiteCutoffContinuumBornDysonGreenLoopMatrix
      side v m probeEnergy broadening disorderStrength hbar pMax
  impurityDensity_pos := hdensity
  impurityStrength_ne_zero := hstrength
  regulator_ne_zero := side.regulator_ne_zero hbroadening
  cutoff_nonneg := hcutoff

@[simp]
theorem finiteCutoffContinuumBornDysonScalarImpurityTMatrixInput_greenLoop
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax
      impurityDensity impurityStrength : ℝ)
    (hbroadening : broadening ≠ 0)
    (hcutoff : 0 ≤ pMax)
    (hdensity : 0 < impurityDensity)
    (hstrength : impurityStrength ≠ 0) :
    (finiteCutoffContinuumBornDysonScalarImpurityTMatrixInput
      side v m probeEnergy broadening disorderStrength hbar pMax
      impurityDensity impurityStrength hbroadening hcutoff hdensity hstrength).greenLoop =
      finiteCutoffContinuumBornDysonGreenLoopMatrix
        side v m probeEnergy broadening disorderStrength hbar pMax :=
  rfl

end

end QuantumTheory.Transport.Models.MassiveDirac
