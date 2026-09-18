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

The algebraic T-matrix data contains only the scalar-impurity parameters. The dressed Green loop is
an explicit argument to the shift, T-matrix, and self-energy definitions, so regulator/cutoff
provenance cannot be attached to an unrelated matrix. The concrete Born-Dyson loop below owns the
finite cutoff, spectral side, broadening, and physical momentum measure.

Invertibility is explicit through `IsUnit`. No geometric-series expansion, small-impurity limit,
self-consistent existence theorem, exact disorder-average identification, or skew-scattering
conductivity is asserted here. The concrete Born-Dyson specialization is an approximation boundary;
it is not identified with the paper-faithful self-consistent T-matrix loop.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Scalar-impurity parameters kept separate from the dressed Green-loop provenance. -/
structure ScalarImpurityParameters where
  /-- Impurity density `n_imp`, kept separate from the aggregate Born disorder strength. -/
  impurityDensity : ℝ
  /-- Scalar single-impurity potential strength `v_imp`. -/
  impurityStrength : ℝ
  /-- The impurity density is positive. -/
  impurityDensity_pos : 0 < impurityDensity
  /-- The scalar impurity potential is nonzero. -/
  impurityStrength_ne_zero : impurityStrength ≠ 0

/-- Matrix shifted by a supplied dressed Green loop, `1 - v_imp G_loop`. -/
def ScalarImpurityParameters.shiftMatrix
    (params : ScalarImpurityParameters) (greenLoop : Matrix2) : Matrix2 :=
  1 - (((params.impurityStrength : ℝ) : ℂ)) • greenLoop

/-- Inverse of the T-matrix shift under an explicit unit hypothesis. -/
noncomputable def ScalarImpurityParameters.inverseShiftMatrix
    (params : ScalarImpurityParameters) (greenLoop : Matrix2)
    (hinvertible : IsUnit (params.shiftMatrix greenLoop)) : Matrix2 :=
  (↑(hinvertible.unit⁻¹) : Matrix2)

/-- Scalar-impurity T-matrix `T = v_imp (1 - v_imp G_loop)⁻¹`. -/
noncomputable def ScalarImpurityParameters.tMatrix
    (params : ScalarImpurityParameters) (greenLoop : Matrix2)
    (hinvertible : IsUnit (params.shiftMatrix greenLoop)) : Matrix2 :=
  (((params.impurityStrength : ℝ) : ℂ)) •
    params.inverseShiftMatrix greenLoop hinvertible

/-- T-matrix self-energy `Σ_T = n_imp T`, with density and single-impurity strength kept distinct. -/
noncomputable def ScalarImpurityParameters.selfEnergy
    (params : ScalarImpurityParameters) (greenLoop : Matrix2)
    (hinvertible : IsUnit (params.shiftMatrix greenLoop)) : Matrix2 :=
  (((params.impurityDensity : ℝ) : ℂ)) • params.tMatrix greenLoop hinvertible

/-- The explicit inverse is a right inverse of `1 - v_imp G_loop`. -/
theorem ScalarImpurityParameters.shiftMatrix_mul_inverseShiftMatrix
    (params : ScalarImpurityParameters) (greenLoop : Matrix2)
    (hinvertible : IsUnit (params.shiftMatrix greenLoop)) :
    params.shiftMatrix greenLoop * params.inverseShiftMatrix greenLoop hinvertible = 1 := by
  simpa [ScalarImpurityParameters.inverseShiftMatrix] using hinvertible.mul_val_inv

/-- The explicit inverse is also a left inverse of `1 - v_imp G_loop`. -/
theorem ScalarImpurityParameters.inverseShiftMatrix_mul_shiftMatrix
    (params : ScalarImpurityParameters) (greenLoop : Matrix2)
    (hinvertible : IsUnit (params.shiftMatrix greenLoop)) :
    params.inverseShiftMatrix greenLoop hinvertible * params.shiftMatrix greenLoop = 1 := by
  simpa [ScalarImpurityParameters.inverseShiftMatrix] using hinvertible.val_inv_mul

/-- Multiplying the T-matrix by its shift from the left gives the scalar impurity potential. -/
theorem ScalarImpurityParameters.shiftMatrix_mul_tMatrix
    (params : ScalarImpurityParameters) (greenLoop : Matrix2)
    (hinvertible : IsUnit (params.shiftMatrix greenLoop)) :
    params.shiftMatrix greenLoop * params.tMatrix greenLoop hinvertible =
      (((params.impurityStrength : ℝ) : ℂ)) • (1 : Matrix2) := by
  unfold ScalarImpurityParameters.tMatrix
  rw [mul_smul_comm, params.shiftMatrix_mul_inverseShiftMatrix greenLoop hinvertible]

/-- Multiplying the T-matrix by its shift from the right gives the same scalar impurity potential. -/
theorem ScalarImpurityParameters.tMatrix_mul_shiftMatrix
    (params : ScalarImpurityParameters) (greenLoop : Matrix2)
    (hinvertible : IsUnit (params.shiftMatrix greenLoop)) :
    params.tMatrix greenLoop hinvertible * params.shiftMatrix greenLoop =
      (((params.impurityStrength : ℝ) : ℂ)) • (1 : Matrix2) := by
  unfold ScalarImpurityParameters.tMatrix
  rw [smul_mul_assoc, params.inverseShiftMatrix_mul_shiftMatrix greenLoop hinvertible]

/-- Exact Lippmann--Schwinger fixed-point identity. This follows from invertibility alone and does
not assert convergence of a geometric series. -/
theorem ScalarImpurityParameters.tMatrix_eq_bare_add_loop_tMatrix
    (params : ScalarImpurityParameters) (greenLoop : Matrix2)
    (hinvertible : IsUnit (params.shiftMatrix greenLoop)) :
    params.tMatrix greenLoop hinvertible =
      (((params.impurityStrength : ℝ) : ℂ)) • (1 : Matrix2) +
        (((params.impurityStrength : ℝ) : ℂ)) •
          (greenLoop * params.tMatrix greenLoop hinvertible) := by
  have h := params.shiftMatrix_mul_tMatrix greenLoop hinvertible
  rw [ScalarImpurityParameters.shiftMatrix] at h
  simp only [sub_mul, one_mul, smul_mul_assoc] at h
  exact (sub_eq_iff_eq_add).mp h

/-- Exact remainder after subtracting the bare scalar-impurity term. No series
expansion is used. -/
theorem ScalarImpurityParameters.tMatrix_sub_bare_eq
    (params : ScalarImpurityParameters) (greenLoop : Matrix2)
    (hinvertible : IsUnit (params.shiftMatrix greenLoop)) :
    params.tMatrix greenLoop hinvertible -
        (((params.impurityStrength : ℝ) : ℂ)) • (1 : Matrix2) =
      (((params.impurityStrength : ℝ) : ℂ)) •
        (greenLoop * params.tMatrix greenLoop hinvertible) := by
  rw [params.tMatrix_eq_bare_add_loop_tMatrix greenLoop hinvertible]
  simp

/-- The exact T-matrix remainder carries two powers of the impurity strength, up to the norm of
the supplied Green loop and inverse shift. -/
theorem ScalarImpurityParameters.norm_tMatrix_sub_bare_le
    (params : ScalarImpurityParameters) (greenLoop : Matrix2)
    (hinvertible : IsUnit (params.shiftMatrix greenLoop)) :
    ‖params.tMatrix greenLoop hinvertible -
        (((params.impurityStrength : ℝ) : ℂ)) • (1 : Matrix2)‖ ≤
      ‖((params.impurityStrength : ℝ) : ℂ)‖ ^ 2 * ‖greenLoop‖ *
        ‖params.inverseShiftMatrix greenLoop hinvertible‖ := by
  rw [params.tMatrix_sub_bare_eq greenLoop hinvertible, norm_smul]
  calc
    ‖((params.impurityStrength : ℝ) : ℂ)‖ *
        ‖greenLoop * params.tMatrix greenLoop hinvertible‖ ≤
      ‖((params.impurityStrength : ℝ) : ℂ)‖ *
        (‖greenLoop‖ * ‖params.tMatrix greenLoop hinvertible‖) :=
      mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
    _ = ‖((params.impurityStrength : ℝ) : ℂ)‖ ^ 2 * ‖greenLoop‖ *
        ‖params.inverseShiftMatrix greenLoop hinvertible‖ := by
      rw [ScalarImpurityParameters.tMatrix, norm_smul]
      ring

/-- With a supplied uniform bound on the inverse shift, the exact remainder has an explicit
quadratic impurity-strength bound. -/
theorem ScalarImpurityParameters.norm_tMatrix_sub_bare_le_of_inverse_bound
    (params : ScalarImpurityParameters) (greenLoop : Matrix2)
    (hinvertible : IsUnit (params.shiftMatrix greenLoop))
    (inverseBound : ℝ)
    (hinverse :
      ‖params.inverseShiftMatrix greenLoop hinvertible‖ ≤ inverseBound) :
    ‖params.tMatrix greenLoop hinvertible -
        (((params.impurityStrength : ℝ) : ℂ)) • (1 : Matrix2)‖ ≤
      ‖((params.impurityStrength : ℝ) : ℂ)‖ ^ 2 * ‖greenLoop‖ * inverseBound := by
  exact (params.norm_tMatrix_sub_bare_le greenLoop hinvertible).trans
    (mul_le_mul_of_nonneg_left hinverse
      (mul_nonneg (sq_nonneg _) (norm_nonneg _)))

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

end QuantumTheory.Transport.Models.MassiveDirac
