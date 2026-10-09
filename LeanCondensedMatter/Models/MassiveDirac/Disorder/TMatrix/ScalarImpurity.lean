import LeanCondensedMatter.Models.MassiveDirac.Model.Operator
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Scalar-impurity T-matrix with a supplied Green loop

The scalar-impurity construction is T = v_imp (1 - v_imp G_loop)⁻¹ and Σ_T = n_imp T.
The loop is an explicit 2×2 matrix argument. Invertibility is supplied through IsUnit;
operator-norm estimates and the quadratic small-strength remainder use the same fixed loop.

The impurity-density and single-impurity-strength convention follows Onoda, Sugimoto, and Nagaosa,
Phys. Rev. Lett. 97, 126602 (2006), Eqs. (12)–(15), doi:10.1103/PhysRevLett.97.126602.
No spectral regulator, momentum measure, cutoff, or self-consistent loop is chosen here.
-/

namespace QuantumTheory.Models.MassiveDirac

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

/-- Exact separation of the scalar mean-potential term from the T-matrix self-energy.
The first term is `n_imp v_imp I`; the second keeps the full T-matrix remainder explicit rather
than identifying the mean term with the zero-mean Born disorder self-energy. -/
theorem ScalarImpurityParameters.selfEnergy_eq_meanPotential_add_tMatrix_remainder
    (params : ScalarImpurityParameters) (greenLoop : Matrix2)
    (hinvertible : IsUnit (params.shiftMatrix greenLoop)) :
    params.selfEnergy greenLoop hinvertible =
      (((params.impurityDensity : ℝ) : ℂ)) •
          ((((params.impurityStrength : ℝ) : ℂ)) • (1 : Matrix2)) +
        (((params.impurityDensity : ℝ) : ℂ)) •
          (params.tMatrix greenLoop hinvertible -
            (((params.impurityStrength : ℝ) : ℂ)) • (1 : Matrix2)) := by
  unfold ScalarImpurityParameters.selfEnergy
  module

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
  have hofReal :
      Tendsto (fun impurityStrength : ℝ => (impurityStrength : ℂ)) (𝓝 0) (𝓝 0) := by
    simpa using Complex.continuous_ofReal.tendsto 0
  have hzero :
      Tendsto
        (fun impurityStrength : ℝ =>
          (((impurityStrength : ℝ) : ℂ)) • matrixOperator greenLoop)
        (𝓝 0) (𝓝 0) := by
    simpa using hofReal.smul_const (matrixOperator greenLoop)
  have hnorm :
      Tendsto
        (fun impurityStrength : ℝ =>
          ‖(((impurityStrength : ℝ) : ℂ)) • matrixOperator greenLoop‖)
        (𝓝 0) (𝓝 0) := by
    simpa [Function.comp_def] using
      (continuous_norm.tendsto
        (0 : DiracHilbert →L[ℂ] DiracHilbert)).comp hzero
  have hsmall :
      ∀ᶠ impurityStrength : ℝ in 𝓝 0,
        ‖(((impurityStrength : ℝ) : ℂ)) • matrixOperator greenLoop‖ < 1 :=
    hnorm (Iio_mem_nhds zero_lt_one)
  let φ : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert) := Matrix.toEuclideanCLM
  filter_upwards [hsmall] with impurityStrength hstrength
  have hoperator :
      IsUnit
        ((1 : DiracHilbert →L[ℂ] DiracHilbert) -
          (((impurityStrength : ℝ) : ℂ)) • matrixOperator greenLoop) :=
    isUnit_one_sub_of_norm_lt_one hstrength
  have hmap :
      φ ((1 : Matrix2) - (((impurityStrength : ℝ) : ℂ)) • greenLoop) =
        (1 : DiracHilbert →L[ℂ] DiracHilbert) -
          (((impurityStrength : ℝ) : ℂ)) • matrixOperator greenLoop := by
    simp only [φ, matrixOperator, map_sub, map_one, map_smul]
  apply (isUnit_map_iff φ
    ((1 : Matrix2) - (((impurityStrength : ℝ) : ℂ)) • greenLoop)).mp
  rw [hmap]
  exact hoperator

/-- The total ring inverse of the operator shift is uniformly bounded on some neighborhood of zero
impurity strength. On that neighborhood the preceding theorem guarantees that this totalized
inverse is the ordinary inverse of a unit. -/
theorem exists_eventually_norm_scalarImpurityShiftOperator_inverse_le
    (greenLoop : Matrix2) :
    ∃ C : ℝ, ∀ᶠ impurityStrength : ℝ in 𝓝 0,
      ‖Ring.inverse
          ((1 : DiracHilbert →L[ℂ] DiracHilbert) -
            (((impurityStrength : ℝ) : ℂ)) • matrixOperator greenLoop)‖ ≤ C := by
  have hofReal :
      Tendsto (fun impurityStrength : ℝ => (impurityStrength : ℂ)) (𝓝 0) (𝓝 0) := by
    simpa using Complex.continuous_ofReal.tendsto 0
  have hzero :
      Tendsto
        (fun impurityStrength : ℝ =>
          (((impurityStrength : ℝ) : ℂ)) • matrixOperator greenLoop)
        (𝓝 0) (𝓝 0) := by
    simpa using hofReal.smul_const (matrixOperator greenLoop)
  rcases
      ((NormedRing.inverse_one_sub_norm
        (R := DiracHilbert →L[ℂ] DiracHilbert)).comp_tendsto hzero).bound with
    ⟨C, hC⟩
  refine ⟨C, ?_⟩
  filter_upwards [hC] with impurityStrength hbound
  simpa [Function.comp_def] using hbound

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
  have hshift_eq :
      matrixOperator (params.shiftMatrix greenLoop) =
        (1 : DiracHilbert →L[ℂ] DiracHilbert) -
          (((params.impurityStrength : ℝ) : ℂ)) • matrixOperator greenLoop := by
    simp only [ScalarImpurityParameters.shiftMatrix, matrixOperator, map_sub, map_one, map_smul]
  have hinverse_eq' :
      matrixOperator (params.inverseShiftMatrix greenLoop hinvertible) =
        Ring.inverse
          ((1 : DiracHilbert →L[ℂ] DiracHilbert) -
            (((params.impurityStrength : ℝ) : ℂ)) • matrixOperator greenLoop) := by
    dsimp [inverseOp, shiftOp] at hinverse_eq
    rw [hshift_eq] at hinverse_eq
    exact hinverse_eq
  rw [ScalarImpurityParameters.tMatrix]
  have hmap_smul :
      matrixOperator
          ((((params.impurityStrength : ℝ) : ℂ)) •
            params.inverseShiftMatrix greenLoop hinvertible) =
        (((params.impurityStrength : ℝ) : ℂ)) •
          matrixOperator (params.inverseShiftMatrix greenLoop hinvertible) := by
    simp only [matrixOperator, map_smul]
  rw [hmap_smul, hinverse_eq']

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
  have hofReal :
      Tendsto (fun impurityStrength : ℝ => (impurityStrength : ℂ)) (𝓝 0) (𝓝 0) := by
    simpa using Complex.continuous_ofReal.tendsto 0
  have hbase :
      Tendsto
        (fun impurityStrength : ℝ =>
          (((impurityStrength : ℝ) : ℂ)) • matrixOperator greenLoop)
        (𝓝 0) (𝓝 0) := by
    simpa using hofReal.smul_const (matrixOperator greenLoop)
  have hzero :
      Tendsto
        (fun impurityStrength : ℝ =>
          -((((impurityStrength : ℝ) : ℂ)) • matrixOperator greenLoop))
        (𝓝 0) (𝓝 0) := by
    simpa using hbase.neg
  have hinverse :=
    (NormedRing.inverse_add_norm_diff_first_order
      (R := DiracHilbert →L[ℂ] DiracHilbert)
      (1 : (DiracHilbert →L[ℂ] DiracHilbert)ˣ)).comp_tendsto hzero
  rcases isBigO_iff'.mp hinverse with ⟨C, _hCpos, hC⟩
  refine IsBigO.of_bound (C * ‖matrixOperator greenLoop‖) ?_
  filter_upwards [hC] with impurityStrength hbound
  have hbound' :
      ‖Ring.inverse
            ((1 : DiracHilbert →L[ℂ] DiracHilbert) -
              (((impurityStrength : ℝ) : ℂ)) • matrixOperator greenLoop) -
          (1 : DiracHilbert →L[ℂ] DiracHilbert)‖ ≤
        C * ‖(((impurityStrength : ℝ) : ℂ)) • matrixOperator greenLoop‖ := by
    simpa [Function.comp_def, sub_eq_add_neg, norm_neg, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)] using hbound
  rw [← smul_sub, norm_smul]
  calc
    ‖((impurityStrength : ℝ) : ℂ)‖ *
        ‖Ring.inverse
            ((1 : DiracHilbert →L[ℂ] DiracHilbert) -
              (((impurityStrength : ℝ) : ℂ)) • matrixOperator greenLoop) -
          (1 : DiracHilbert →L[ℂ] DiracHilbert)‖ ≤
      ‖((impurityStrength : ℝ) : ℂ)‖ *
        (C * ‖(((impurityStrength : ℝ) : ℂ)) • matrixOperator greenLoop‖) :=
      mul_le_mul_of_nonneg_left hbound' (norm_nonneg _)
    _ = (C * ‖matrixOperator greenLoop‖) * ‖impurityStrength ^ 2‖ := by
      rw [norm_smul]
      simp only [Complex.norm_real, Real.norm_eq_abs, norm_pow]
      ring


end

end QuantumTheory.Models.MassiveDirac
