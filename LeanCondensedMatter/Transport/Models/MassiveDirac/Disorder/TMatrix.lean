import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningBornRealSpacePropagator
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Analysis.Normed.Ring.Units

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
open Asymptotics Filter Topology

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
  have h := params.tMatrix_eq_bare_add_loop_tMatrix greenLoop hinvertible
  calc
    params.tMatrix greenLoop hinvertible -
        (((params.impurityStrength : ℝ) : ℂ)) • (1 : Matrix2) =
      ((((params.impurityStrength : ℝ) : ℂ)) • (1 : Matrix2) +
          (((params.impurityStrength : ℝ) : ℂ)) •
            (greenLoop * params.tMatrix greenLoop hinvertible)) -
        (((params.impurityStrength : ℝ) : ℂ)) • (1 : Matrix2) :=
      congrArg
        (fun M : Matrix2 =>
          M - (((params.impurityStrength : ℝ) : ℂ)) • (1 : Matrix2))
        h
    _ = (((params.impurityStrength : ℝ) : ℂ)) •
        (greenLoop * params.tMatrix greenLoop hinvertible) := by
      abel

/-- In operator norm, the exact T-matrix remainder carries two powers of the impurity strength, up
to the norm of the supplied Green loop and inverse shift. -/
theorem ScalarImpurityParameters.norm_matrixOperator_tMatrix_sub_bare_le
    (params : ScalarImpurityParameters) (greenLoop : Matrix2)
    (hinvertible : IsUnit (params.shiftMatrix greenLoop)) :
    ‖matrixOperator
        (params.tMatrix greenLoop hinvertible -
          (((params.impurityStrength : ℝ) : ℂ)) • (1 : Matrix2))‖ ≤
      ‖((params.impurityStrength : ℝ) : ℂ)‖ ^ 2 * ‖matrixOperator greenLoop‖ *
        ‖matrixOperator (params.inverseShiftMatrix greenLoop hinvertible)‖ := by
  have ht :
      matrixOperator (params.tMatrix greenLoop hinvertible) =
        (((params.impurityStrength : ℝ) : ℂ)) •
          matrixOperator (params.inverseShiftMatrix greenLoop hinvertible) := by
    unfold ScalarImpurityParameters.tMatrix matrixOperator
    rw [map_smul]
  rw [params.tMatrix_sub_bare_eq greenLoop hinvertible]
  simp only [matrixOperator, map_smul, map_mul]
  rw [norm_smul]
  calc
    ‖((params.impurityStrength : ℝ) : ℂ)‖ *
        ‖matrixOperator greenLoop * matrixOperator (params.tMatrix greenLoop hinvertible)‖ ≤
      ‖((params.impurityStrength : ℝ) : ℂ)‖ *
        (‖matrixOperator greenLoop‖ *
          ‖matrixOperator (params.tMatrix greenLoop hinvertible)‖) :=
      mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
    _ = ‖((params.impurityStrength : ℝ) : ℂ)‖ ^ 2 * ‖matrixOperator greenLoop‖ *
        ‖matrixOperator (params.inverseShiftMatrix greenLoop hinvertible)‖ := by
      rw [ht, norm_smul]
      ring

/-- With a supplied pointwise bound on the operator norm of the inverse shift, the exact remainder
has an explicit quadratic impurity-strength factor. This does not by itself assert a uniform
small-impurity estimate, Big-O statement, or limit as the impurity strength tends to zero. -/
theorem ScalarImpurityParameters.norm_matrixOperator_tMatrix_sub_bare_le_of_inverse_bound
    (params : ScalarImpurityParameters) (greenLoop : Matrix2)
    (hinvertible : IsUnit (params.shiftMatrix greenLoop))
    (inverseBound : ℝ)
    (hinverse :
      ‖matrixOperator (params.inverseShiftMatrix greenLoop hinvertible)‖ ≤ inverseBound) :
    ‖matrixOperator
        (params.tMatrix greenLoop hinvertible -
          (((params.impurityStrength : ℝ) : ℂ)) • (1 : Matrix2))‖ ≤
      ‖((params.impurityStrength : ℝ) : ℂ)‖ ^ 2 * ‖matrixOperator greenLoop‖ *
        inverseBound := by
  exact (params.norm_matrixOperator_tMatrix_sub_bare_le greenLoop hinvertible).trans
    (mul_le_mul_of_nonneg_left hinverse
      (mul_nonneg (sq_nonneg _) (norm_nonneg _)))

/-- For a fixed Green loop, the scalar-impurity shift is a unit for all impurity strengths
sufficiently close to zero. This is a family-level statement in the raw scalar strength, so the
limit point `v_imp = 0` is not excluded by `ScalarImpurityParameters.impurityStrength_ne_zero`. -/
theorem eventually_isUnit_scalarImpurityShiftMatrix (greenLoop : Matrix2) :
    ∀ᶠ impurityStrength : ℝ in 𝓝 0,
      IsUnit
        ((1 : Matrix2) - (((impurityStrength : ℝ) : ℂ)) • greenLoop) := by
  have hzero :
      Tendsto
        (fun impurityStrength : ℝ => impurityStrength • matrixOperator greenLoop)
        (𝓝 0) (𝓝 0) := by
    simpa using
      (continuous_id.smul
        (continuous_const : Continuous
          (fun _ : ℝ => matrixOperator greenLoop))).tendsto 0
  have hnorm :
      Tendsto
        (fun impurityStrength : ℝ =>
          ‖impurityStrength • matrixOperator greenLoop‖)
        (𝓝 0) (𝓝 0) := by
    simpa only [Function.comp_apply, norm_zero] using
      (continuous_norm.tendsto
        (0 : DiracHilbert →L[ℂ] DiracHilbert)).comp hzero
  have hsmall :
      ∀ᶠ impurityStrength : ℝ in 𝓝 0,
        ‖impurityStrength • matrixOperator greenLoop‖ < 1 :=
    hnorm (Iio_mem_nhds zero_lt_one)
  let φ : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert) := Matrix.toEuclideanCLM
  filter_upwards [hsmall] with impurityStrength hstrength
  apply (isUnit_map_iff φ
    ((1 : Matrix2) - (((impurityStrength : ℝ) : ℂ)) • greenLoop)).mp
  simpa only [φ, matrixOperator, map_sub, map_one, map_smul, Complex.coe_smul] using
    (isUnit_one_sub_of_norm_lt_one hstrength)

/-- The total ring inverse of the operator shift is uniformly bounded on some neighborhood of zero
impurity strength. On that neighborhood the preceding theorem guarantees that this totalized
inverse is the ordinary inverse of a unit. -/
theorem exists_eventually_norm_scalarImpurityShiftOperator_inverse_le
    (greenLoop : Matrix2) :
    ∃ C : ℝ, ∀ᶠ impurityStrength : ℝ in 𝓝 0,
      ‖Ring.inverse
          ((1 : DiracHilbert →L[ℂ] DiracHilbert) -
            (((impurityStrength : ℝ) : ℂ)) • matrixOperator greenLoop)‖ ≤ C := by
  have hzero :
      Tendsto
        (fun impurityStrength : ℝ => impurityStrength • matrixOperator greenLoop)
        (𝓝 0) (𝓝 0) := by
    simpa using
      (continuous_id.smul
        (continuous_const : Continuous
          (fun _ : ℝ => matrixOperator greenLoop))).tendsto 0
  rcases
      ((NormedRing.inverse_one_sub_norm
        (R := DiracHilbert →L[ℂ] DiracHilbert)).comp_tendsto hzero).bound with
    ⟨C, hC⟩
  refine ⟨C, ?_⟩
  simpa only [Complex.coe_smul] using hC

/-- On an invertible scalar-impurity shift, the canonical matrix T-matrix becomes the corresponding
totalized operator-ring inverse after applying `matrixOperator`. This connects the family-level
asymptotic route below to the existing `IsUnit`-guarded T-matrix API. -/
theorem ScalarImpurityParameters.matrixOperator_tMatrix_eq_ringInverse_shift
    (params : ScalarImpurityParameters) (greenLoop : Matrix2)
    (hinvertible : IsUnit (params.shiftMatrix greenLoop)) :
    matrixOperator (params.tMatrix greenLoop hinvertible) =
      (((params.impurityStrength : ℝ) : ℂ)) •
        Ring.inverse
          ((1 : DiracHilbert →L[ℂ] DiracHilbert) -
            (((params.impurityStrength : ℝ) : ℂ)) • matrixOperator greenLoop) := by
  let shiftOp : DiracHilbert →L[ℂ] DiracHilbert :=
    matrixOperator (params.shiftMatrix greenLoop)
  let inverseOp : DiracHilbert →L[ℂ] DiracHilbert :=
    matrixOperator (params.inverseShiftMatrix greenLoop hinvertible)
  let φ : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert) := Matrix.toEuclideanCLM
  have hshiftUnit : IsUnit shiftOp := by
    dsimp [shiftOp]
    exact (isUnit_map_iff φ (params.shiftMatrix greenLoop)).mpr hinvertible
  have hinverse_mul : inverseOp * shiftOp = 1 := by
    dsimp [inverseOp, shiftOp]
    simpa [matrixOperator, map_mul, map_one] using
      congrArg matrixOperator
        (params.inverseShiftMatrix_mul_shiftMatrix greenLoop hinvertible)
  have hinverse_eq : inverseOp = Ring.inverse shiftOp := by
    have hmul : shiftOp * Ring.inverse shiftOp = 1 :=
      Ring.mul_inverse_cancel shiftOp hshiftUnit
    calc
      inverseOp = inverseOp * 1 := (mul_one inverseOp).symm
      _ = inverseOp * (shiftOp * Ring.inverse shiftOp) := by rw [hmul]
      _ = (inverseOp * shiftOp) * Ring.inverse shiftOp := by rw [mul_assoc]
      _ = Ring.inverse shiftOp := by rw [hinverse_mul, one_mul]
  have hinverse_eq' :
      Matrix.toEuclideanCLM (params.inverseShiftMatrix greenLoop hinvertible) =
        Ring.inverse
          ((1 : DiracHilbert →L[ℂ] DiracHilbert) -
            (((params.impurityStrength : ℝ) : ℂ)) •
              Matrix.toEuclideanCLM greenLoop) := by
    simpa only [inverseOp, shiftOp, ScalarImpurityParameters.shiftMatrix,
      matrixOperator, map_sub, map_one, map_smul, Complex.coe_smul] using hinverse_eq
  unfold ScalarImpurityParameters.tMatrix matrixOperator
  rw [map_smul, hinverse_eq']

/-- For a fixed Green loop, the operator-valued scalar-impurity T-matrix has a genuine quadratic
remainder at zero impurity strength:
`T(v_imp) - v_imp I = O(v_imp²)`.
The use of `Ring.inverse` only totalizes the family away from the unit neighborhood; locally it is
the ordinary inverse by `eventually_isUnit_scalarImpurityShiftMatrix`. -/
theorem scalarImpurityTMatrixOperator_sub_bare_isBigO_sq
    (greenLoop : Matrix2) :
    (fun impurityStrength : ℝ =>
      (((impurityStrength : ℝ) : ℂ)) •
          Ring.inverse
            ((1 : DiracHilbert →L[ℂ] DiracHilbert) -
              (((impurityStrength : ℝ) : ℂ)) • matrixOperator greenLoop) -
        (((impurityStrength : ℝ) : ℂ)) •
          (1 : DiracHilbert →L[ℂ] DiracHilbert))
      =O[𝓝 0] (fun impurityStrength : ℝ => impurityStrength ^ 2) := by
  simp only [Complex.coe_smul]
  let G : DiracHilbert →L[ℂ] DiracHilbert := matrixOperator greenLoop
  have hbase :
      Tendsto
        (fun impurityStrength : ℝ => impurityStrength • G)
        (𝓝 0) (𝓝 0) := by
    simpa using
      (continuous_id.smul
        (continuous_const : Continuous (fun _ : ℝ => G))).tendsto 0
  have hzero :
      Tendsto
        (fun impurityStrength : ℝ => -(impurityStrength • G))
        (𝓝 0) (𝓝 0) := by
    simpa using hbase.neg
  have hinverse :=
    (NormedRing.inverse_add_norm_diff_first_order
      (R := DiracHilbert →L[ℂ] DiracHilbert)
      (1 : (DiracHilbert →L[ℂ] DiracHilbert)ˣ)).comp_tendsto hzero
  rcases isBigO_iff'.mp hinverse with ⟨C, _hCpos, hC⟩
  refine IsBigO.of_bound (C * ‖G‖) ?_
  filter_upwards [hC] with impurityStrength hbound
  have hbound' :
      ‖Ring.inverse
            ((1 : DiracHilbert →L[ℂ] DiracHilbert) -
              impurityStrength • G) -
          (1 : DiracHilbert →L[ℂ] DiracHilbert)‖ ≤
        C * ‖impurityStrength • G‖ := by
    simpa [Function.comp_apply, sub_eq_add_neg, norm_neg, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)] using hbound
  rw [← smul_sub, norm_smul]
  calc
    ‖((impurityStrength : ℝ) : ℂ)‖ *
        ‖Ring.inverse
            ((1 : DiracHilbert →L[ℂ] DiracHilbert) -
              impurityStrength • G) -
          (1 : DiracHilbert →L[ℂ] DiracHilbert)‖ ≤
      ‖((impurityStrength : ℝ) : ℂ)‖ *
        (C * ‖impurityStrength • G‖) :=
      mul_le_mul_of_nonneg_left hbound' (norm_nonneg _)
    _ = (C * ‖G‖) * ‖impurityStrength ^ 2‖ := by
      rw [norm_smul]
      simp only [Real.norm_eq_abs, norm_pow]
      ring

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
