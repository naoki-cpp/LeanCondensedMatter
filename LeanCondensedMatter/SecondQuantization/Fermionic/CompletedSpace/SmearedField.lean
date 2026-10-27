import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.CanonicalAnticommutationRelations
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Core
import LeanCondensedMatter.Analysis.ScalarExchange.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Topology.DenseEmbedding

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

private theorem createFieldCore_anticomm (v w : Mode →₀ ℂ) :
    ScalarExchange.zetaCommutator (-1 : ℂ) (star (createFieldCore v)) (createFieldCore w) =
      inner ℂ (Common.algebraicToCompleted v) (Common.algebraicToCompleted w) •
        ContinuousLinearMap.id ℂ (CompletedFockSpace Mode) := by
  classical
  have hscalar : (∑ i ∈ v.support, star (v i) * w i) =
      inner ℂ (Common.algebraicToCompleted v) (Common.algebraicToCompleted w) := by
    rw [lp.inner_eq_tsum]
    change (∑ i ∈ v.support, star (v i) * w i) = ∑' i, inner ℂ (v i) (w i)
    simp only [RCLike.inner_apply]
    symm
    calc
      _ = ∑ i ∈ v.support, w i * (starRingEnd ℂ) (v i) := by
        apply tsum_eq_sum
        intro i hi
        simp only [Finsupp.notMem_support_iff.mp hi, map_zero, mul_zero]
      _ = _ := Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h := ScalarExchange.zetaCommutator_sum_sum (-1 : ℂ) v.support w.support
    (fun i => star (v i) • completedAnnihilate i)
    (fun j => w j • completedCreate j)
  simp only [ScalarExchange.zetaCommutator_smul_smul,
    completedAnticomm_annihilate_create] at h
  have hsum : (∑ i ∈ v.support, ∑ j ∈ w.support,
      (star (v i) * w j) •
        (if i = j then ContinuousLinearMap.id ℂ (CompletedFockSpace Mode) else 0)) =
      (∑ i ∈ v.support, star (v i) * w i) •
        ContinuousLinearMap.id ℂ (CompletedFockSpace Mode) := by
    rw [Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ w.support
    · simp [smul_ite, hi]
    · simp [smul_ite, hi, Finsupp.notMem_support_iff.mp hi]
  rw [hsum, hscalar] at h
  simpa only [createFieldCore, Finsupp.linearCombination_apply, Finsupp.sum,
    star_sum, star_smul, star_completedCreate] using h

private theorem norm_createFieldCore_le (v : Mode →₀ ℂ) :
    ‖createFieldCore v‖ ≤ ‖Common.algebraicToCompleted v‖ := by
  classical
  let C := createFieldCore v
  let u := Common.algebraicToCompleted v
  have hcar : star C * C + C * star C = ((‖u‖ ^ (2 : ℕ) : ℝ) : ℂ) •
      ContinuousLinearMap.id ℂ (CompletedFockSpace Mode) := by
    have hnorm : inner ℂ u u = ((‖u‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
      convert! (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) u) using 1
      simp only [Complex.ofReal_pow]
      with_unfolding_all rfl
    have h := createFieldCore_anticomm v v
    rw [hnorm] at h
    simpa only [ScalarExchange.zetaCommutator, neg_one_smul, sub_neg_eq_add] using h
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

/-- Creation fields anticommute for arbitrary square-summable one-particle coefficients. -/
theorem completedAnticomm_createField_createField (v w : Common.CompletedFock Mode) :
    ScalarExchange.zetaCommutator (-1 : ℂ) (completedCreateField v)
      (completedCreateField w) = 0 := by
  classical
  refine Common.algebraicToCompleted_denseRange.induction_on₂ ?_ ?_ v w
  · apply isClosed_eq
    · unfold ScalarExchange.zetaCommutator
      fun_prop
    · fun_prop
  · intro a b
    rw [completedCreateField_algebraicToCompleted, completedCreateField_algebraicToCompleted,
      ScalarExchange.zetaCommutator_sum_sum]
    simp only [ScalarExchange.zetaCommutator_smul_smul, completedAnticomm_create_create,
      smul_zero, Finset.sum_const_zero]

/-- The mixed CAR for square-summable coefficients: `{c(v)†, c(w)} = ⟨v,w⟩ I`, where
`c` denotes the creation field and the inner product is conjugate-linear in its first argument. -/
theorem completedAnticomm_adjoint_createField (v w : Common.CompletedFock Mode) :
    ScalarExchange.zetaCommutator (-1 : ℂ) (star (completedCreateField v))
      (completedCreateField w) =
        inner ℂ v w • ContinuousLinearMap.id ℂ (CompletedFockSpace Mode) := by
  refine Common.algebraicToCompleted_denseRange.induction_on₂ ?_ ?_ v w
  · apply isClosed_eq
    · unfold ScalarExchange.zetaCommutator
      fun_prop
    · fun_prop
  · intro a b
    simpa only [completedCreateField_algebraicToCompleted, createFieldCore,
      Finsupp.linearCombination_apply, Finsupp.sum] using createFieldCore_anticomm a b

/-- The adjoint creation field annihilates the vacuum, including for infinite-support
one-particle coefficients. -/
theorem adjoint_completedCreateField_vacuum (v : Common.CompletedFock Mode) :
    star (completedCreateField v) (completedBasisState (vacuum : Occupation Mode)) = 0 := by
  classical
  refine Common.algebraicToCompleted_denseRange.induction_on v ?_ ?_
  · apply isClosed_eq <;> fun_prop
  · intro a
    simp [completedCreateField_algebraicToCompleted, star_sum, star_smul,
      star_completedCreate, vacuum]

/-- Creating from the vacuum preserves the one-particle inner product. -/
theorem inner_completedCreateField_vacuum (v w : Common.CompletedFock Mode) :
    inner ℂ (completedCreateField v (completedBasisState (vacuum : Occupation Mode)))
      (completedCreateField w (completedBasisState (vacuum : Occupation Mode))) =
        inner ℂ v w := by
  have h := congrArg (fun T : CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode =>
    T (completedBasisState (vacuum : Occupation Mode)))
      (completedAnticomm_adjoint_createField v w)
  simp only [ScalarExchange.zetaCommutator, neg_one_smul, sub_neg_eq_add, add_apply,
    mul_apply_eq_comp, smul_apply, ContinuousLinearMap.id_apply,
    adjoint_completedCreateField_vacuum, map_zero, add_zero] at h
  rw [← ContinuousLinearMap.adjoint_inner_right (completedCreateField v),
    ← ContinuousLinearMap.star_eq_adjoint, h, inner_smul_right,
    inner_completedBasisState_left]
  simp [completedBasisState]

end

end SecondQuantization.Fermionic
