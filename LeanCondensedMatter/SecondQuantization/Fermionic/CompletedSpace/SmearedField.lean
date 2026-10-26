import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.CanonicalAnticommutationRelations
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Core
import LeanCondensedMatter.Analysis.ScalarExchange.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option linter.style.header false

/-!
# Completed fermionic creation fields with square-summable coefficients

Finite linear combinations of mode creation operators satisfy the CAR norm bound in the
one-particle ℓ² norm. Mathlib's dense linear extension therefore supplies a bounded creation
field for arbitrary square-summable mode coefficients, including vectors with infinite support.
Annihilation is the Hilbert adjoint of this field. This is a prerequisite for lifting unitaries
which mix infinitely many modes; it is not yet that Fock lift.
-/

namespace SecondQuantization.Fermionic

open scoped BigOperators

noncomputable section

variable {Mode : Type*} [LinearOrder Mode]

private def createFieldCore : (Mode →₀ ℂ) →ₗ[ℂ]
    (CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode) :=
  Finsupp.linearCombination ℂ completedCreate

private theorem norm_createFieldCore_le (v : Mode →₀ ℂ) :
    ‖createFieldCore v‖ ≤ ‖Common.algebraicToCompleted v‖ := by
  classical
  let C := createFieldCore v
  let u := Common.algebraicToCompleted v
  have hscalar : (∑ i ∈ v.support, star (v i) * v i) = ((‖u‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    calc
      _ = inner ℂ u u := by
        rw [lp.inner_eq_tsum]
        change (∑ i ∈ v.support, star (v i) * v i) = ∑' i, inner ℂ (v i) (v i)
        simp only [RCLike.inner_apply]
        symm
        calc
          _ = ∑ i ∈ v.support, v i * (starRingEnd ℂ) (v i) := by
            apply tsum_eq_sum
            intro i hi
            simp only [Finsupp.notMem_support_iff.mp hi, map_zero, zero_mul]
          _ = _ := Finset.sum_congr rfl fun i _ => mul_comm _ _
      _ = _ := by
        convert! (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) u) using 1 <;>
          simp only [Complex.ofReal_pow] <;> with_unfolding_all rfl
  have hcar : star C * C + C * star C = ((‖u‖ ^ (2 : ℕ) : ℝ) : ℂ) •
      ContinuousLinearMap.id ℂ (CompletedFockSpace Mode) := by
    have h := ScalarExchange.zetaCommutator_sum_sum (-1 : ℂ) v.support v.support
      (fun i => star (v i) • completedAnnihilate i)
      (fun j => v j • completedCreate j)
    simp only [ScalarExchange.zetaCommutator_smul_smul,
      completedAnticomm_annihilate_create] at h
    have hsum : (∑ i ∈ v.support, ∑ j ∈ v.support,
        (star (v i) * v j) •
          (if i = j then ContinuousLinearMap.id ℂ (CompletedFockSpace Mode) else 0)) =
        (∑ i ∈ v.support, star (v i) * v i) •
          ContinuousLinearMap.id ℂ (CompletedFockSpace Mode) := by
      rw [Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro i hi
      simp [smul_ite, hi]
    rw [hsum, hscalar] at h
    simpa only [C, createFieldCore, Finsupp.linearCombination_apply, Finsupp.sum,
      star_sum, star_smul, star_completedCreate, ScalarExchange.zetaCommutator,
      neg_one_smul, sub_neg_eq_add] using h
  apply C.opNorm_le_bound (norm_nonneg u)
  intro x
  have hinner := congrArg (fun T : CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode =>
    inner ℂ x (T x)) hcar
  simp only [add_apply, mul_apply_eq_comp, smul_apply, ContinuousLinearMap.id_apply,
    inner_add_right, inner_smul_right] at hinner
  simp only [ContinuousLinearMap.star_eq_adjoint] at hinner
  rw [ContinuousLinearMap.adjoint_inner_right C x (C x),
    ← ContinuousLinearMap.adjoint_inner_left C ((ContinuousLinearMap.adjoint C) x) x] at hinner
  simp only [inner_self_eq_norm_sq_to_K] at hinner
  have hreal : ‖C x‖ ^ 2 + ‖(ContinuousLinearMap.adjoint C) x‖ ^ 2 =
      ‖u‖ ^ 2 * ‖x‖ ^ 2 := by
    apply Complex.ofReal_injective
    convert! hinner using 1 <;>
      simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow] <;>
        with_unfolding_all rfl
  nlinarith [sq_nonneg ‖(ContinuousLinearMap.adjoint C) x‖,
    norm_nonneg (C x), mul_nonneg (norm_nonneg u) (norm_nonneg x)]

/-- Creation smeared with square-summable one-particle mode coefficients. The mode type may be
infinite. The extension is in operator norm, and its Hilbert adjoint gives annihilation. -/
def completedCreateField : Common.CompletedFock Mode →L[ℂ]
    (CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode) :=
  createFieldCore.extendOfNorm (Common.algebraicToCompleted (Config := Mode))

/-- The completed field extends the finite-support sum of the existing mode operators. -/
theorem completedCreateField_algebraicToCompleted (v : Mode →₀ ℂ) :
    completedCreateField (Common.algebraicToCompleted v) =
      ∑ i ∈ v.support, v i • completedCreate i := by
  exact LinearMap.extendOfNorm_eq Common.algebraicToCompleted_denseRange
    ⟨1, fun v => by simpa only [one_mul] using norm_createFieldCore_le v⟩ v

/-- The creation field is bounded by the one-particle Hilbert norm, independently of support size. -/
theorem norm_completedCreateField_le (v : Common.CompletedFock Mode) :
    ‖completedCreateField v‖ ≤ ‖v‖ := by
  simpa only [completedCreateField, one_mul] using LinearMap.norm_extendOfNorm_apply_le
    (f := createFieldCore) Common.algebraicToCompleted_denseRange 1
    (fun v => by simpa only [one_mul] using norm_createFieldCore_le v) v

/-- A mode basis vector recovers the original completed creation operator. -/
@[simp]
theorem completedCreateField_basisState (i : Mode) :
    completedCreateField (Common.completedBasisState i) = completedCreate i := by
  rw [← Common.algebraicToCompleted_basisState, completedCreateField_algebraicToCompleted]
  simp [Common.basisState]

end

end SecondQuantization.Fermionic
