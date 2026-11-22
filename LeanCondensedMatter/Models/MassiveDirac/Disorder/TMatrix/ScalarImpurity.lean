import LeanCondensedMatter.Transport.Disorder.TMatrix
import LeanCondensedMatter.Models.MassiveDirac.Model.Operator
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Scalar-impurity T-matrix with a supplied Green loop

The scalar-impurity construction is T = v_imp (1 - v_imp G_loop)⁻¹ and Σ_T = n_imp T.
The loop is an explicit 2×2 matrix argument. Invertibility is supplied through IsUnit;
the quadratic small-strength remainder uses the same fixed loop.

The impurity-density and single-impurity-strength convention follows Onoda, Sugimoto, and Nagaosa,
Phys. Rev. Lett. 97, 126602 (2006), Eqs. (12)–(15), doi:10.1103/PhysRevLett.97.126602.
No spectral regulator, momentum measure, cutoff, or self-consistent loop is chosen here.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

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

/-- Scalar-impurity T-matrix `T = v_imp (1 - v_imp G_loop)⁻¹`. -/
noncomputable def ScalarImpurityParameters.tMatrix
    (params : ScalarImpurityParameters) (greenLoop : Matrix2)
    (hinvertible : IsUnit (params.shiftMatrix greenLoop)) : Matrix2 :=
  QuantumTheory.Transport.scalarImpurityTMatrix
    ((params.impurityStrength : ℝ) : ℂ) greenLoop hinvertible

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
