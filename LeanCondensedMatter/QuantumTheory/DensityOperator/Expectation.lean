import LeanCondensedMatter.QuantumTheory.DensityOperator.Basic

/-!
# Expectations of bounded operators

A density operator defines a normalized continuous complex-linear functional on bounded operators.
The definition uses the density operator's spectral decomposition, so the observed operator need
not be compact, self-adjoint, or trace-class.
-/

noncomputable section

namespace QuantumTheory

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
private theorem norm_inner_apply_le_opNorm_of_norm_eq_one
    (A : H →L[ℂ] H) {x : H} (hx : ‖x‖ = 1) :
    ‖(inner ℂ x (A x) : ℂ)‖ ≤ ‖A‖ := by
  calc
    ‖(inner ℂ x (A x) : ℂ)‖ ≤ ‖x‖ * ‖A x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖A‖ * ‖x‖) := by
      gcongr
      exact A.le_opNorm _
    _ = ‖A‖ := by rw [hx]; ring

/-- The spectral series defining the expectation of a bounded operator is summable. -/
theorem DensityOperator.summable_expectation_term (ρ : DensityOperator H) (A : H →L[ℂ] H) :
    Summable (fun a : EigenvectorIndex ρ.op => (a.1.1 : ℂ) *
      (inner ℂ (eigenvectorFamily ρ.spectralTraceClass.compact a)
        (A (eigenvectorFamily ρ.spectralTraceClass.compact a)) : ℂ)) := by
  have hnorm := eigenvectorFamily_norm_eq_one ρ
  refine Summable.of_norm_bounded
    (ρ.spectralTraceClass.summable.mul_right ‖A‖) fun a => ?_
  have hle := norm_inner_apply_le_opNorm_of_norm_eq_one A (hnorm a)
  rw [norm_mul, Complex.norm_real]
  exact mul_le_mul_of_nonneg_left hle (abs_nonneg _)

/-- The absolute eigenvalue weights of a density operator sum to one. -/
theorem DensityOperator.hasSum_abs_eigenvalues_eq_one (ρ : DensityOperator H) :
    HasSum (fun a : EigenvectorIndex ρ.op => |a.1.1|) 1 := by
  have hsum : HasSum (fun a : EigenvectorIndex ρ.op => a.1.1) 1 := by
    have h := (summable_eigenvectorIndex ρ.spectralTraceClass.summable).hasSum
    have htrace : (∑' a : EigenvectorIndex ρ.op, a.1.1) = 1 := by
      simpa [spectralTrace] using ρ.spectralTrace_op_eq_one
    rwa [htrace] at h
  exact HasSum.congr_fun hsum fun a =>
    abs_of_nonneg (eigenvalue_nonneg_of_isPositive ρ.pos.toLinearMap a)

/-- The unbundled complex expectation value used to construct `DensityOperator.expectation`. -/
private noncomputable def densityExpectation (ρ : DensityOperator H) (A : H →L[ℂ] H) : ℂ :=
  ∑' a : EigenvectorIndex ρ.op, (a.1.1 : ℂ) *
    (inner ℂ (eigenvectorFamily ρ.spectralTraceClass.compact a)
      (A (eigenvectorFamily ρ.spectralTraceClass.compact a)) : ℂ)

private theorem densityExpectation_add (ρ : DensityOperator H) (A B : H →L[ℂ] H) :
    densityExpectation ρ (A + B) = densityExpectation ρ A + densityExpectation ρ B := by
  rw [densityExpectation, densityExpectation, densityExpectation,
    ← ((ρ.summable_expectation_term A).hasSum.add
      (ρ.summable_expectation_term B).hasSum).tsum_eq]
  apply tsum_congr
  intro a
  simp [inner_add_right, mul_add]

private theorem densityExpectation_smul (ρ : DensityOperator H) (c : ℂ) (A : H →L[ℂ] H) :
    densityExpectation ρ (c • A) = c * densityExpectation ρ A := by
  rw [densityExpectation, densityExpectation,
    ← ((ρ.summable_expectation_term A).hasSum.mul_left c).tsum_eq]
  apply tsum_congr
  intro a
  simp [inner_smul_right]
  ring

private theorem densityExpectation_norm_le (ρ : DensityOperator H) (A : H →L[ℂ] H) :
    ‖densityExpectation ρ A‖ ≤ ‖A‖ := by
  rw [densityExpectation]
  have hsum : HasSum (fun a : EigenvectorIndex ρ.op => |a.1.1| * ‖A‖) (1 * ‖A‖) :=
    (ρ.hasSum_abs_eigenvalues_eq_one).mul_right ‖A‖
  have hbound :
      ‖∑' a : EigenvectorIndex ρ.op, (a.1.1 : ℂ) *
        (inner ℂ (eigenvectorFamily ρ.spectralTraceClass.compact a)
          (A (eigenvectorFamily ρ.spectralTraceClass.compact a)) : ℂ)‖ ≤ 1 * ‖A‖ := by
    apply tsum_of_norm_bounded hsum
    intro a
    have hle := norm_inner_apply_le_opNorm_of_norm_eq_one A (eigenvectorFamily_norm_eq_one ρ a)
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_left hle (abs_nonneg _)
  simpa using hbound

/-- The normalized complex expectation functional associated with a density operator. -/
noncomputable def DensityOperator.expectation (ρ : DensityOperator H) :
    (H →L[ℂ] H) →L[ℂ] ℂ :=
  IsBoundedLinearMap.toContinuousLinearMap
    (fun A : H →L[ℂ] H => densityExpectation ρ A)
    { map_add := densityExpectation_add ρ
      map_smul := fun c A => by
        simpa only [smul_eq_mul] using densityExpectation_smul ρ c A
      bound := ⟨1, zero_lt_one, fun A => by simpa using densityExpectation_norm_le ρ A⟩ }

theorem DensityOperator.expectation_apply (ρ : DensityOperator H) (A : H →L[ℂ] H) :
    ρ.expectation A =
      ∑' a : EigenvectorIndex ρ.op, (a.1.1 : ℂ) *
        (inner ℂ (eigenvectorFamily ρ.spectralTraceClass.compact a)
          (A (eigenvectorFamily ρ.spectralTraceClass.compact a)) : ℂ) :=
  rfl

/-- Expectations are contractive in the operator norm. -/
theorem DensityOperator.norm_expectation_le (ρ : DensityOperator H) (A : H →L[ℂ] H) :
    ‖ρ.expectation A‖ ≤ ‖A‖ :=
  densityExpectation_norm_le ρ A

/-- The expectation of the identity operator is one. -/
@[simp]
theorem DensityOperator.expectation_id (ρ : DensityOperator H) :
    ρ.expectation (ContinuousLinearMap.id ℂ H) = 1 := by
  rw [ρ.expectation_apply]
  calc
    (∑' a : EigenvectorIndex ρ.op, (a.1.1 : ℂ) *
      inner ℂ (eigenvectorFamily ρ.spectralTraceClass.compact a)
        ((ContinuousLinearMap.id ℂ H) (eigenvectorFamily ρ.spectralTraceClass.compact a))) =
        ∑' a : EigenvectorIndex ρ.op, (a.1.1 : ℂ) := by
      apply tsum_congr
      intro a
      rw [ContinuousLinearMap.id_apply, inner_self_eq_norm_sq_to_K,
        eigenvectorFamily_norm_eq_one ρ a]
      norm_num
    _ = 1 := by
      have htrace : (∑' a : EigenvectorIndex ρ.op, a.1.1) = 1 := by
        simpa [spectralTrace] using ρ.spectralTrace_op_eq_one
      exact_mod_cast htrace

end QuantumTheory
