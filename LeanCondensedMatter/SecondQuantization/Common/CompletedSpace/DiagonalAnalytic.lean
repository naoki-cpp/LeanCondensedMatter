import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.Diagonal
import LeanCondensedMatter.Analysis.Operator.Positive
import Mathlib.Analysis.InnerProductSpace.LinearPMap

set_option linter.style.header false

/-!
# Analytic properties of generic completed diagonal operators

This file owns the statistics-independent analytic theory of maximal diagonal multiplication
operators on `Common.CompletedFock Config`: dense domain, closedness, exact adjoint, and
self-adjointness for conjugation-fixed weights.
-/

namespace SecondQuantization
namespace Common

noncomputable section

variable {Config : Type*}

/-- Uniformly bounded diagonal multiplication by nonnegative real weights is positive. -/
theorem completedBoundedDiagonalOperator_isPositive_of_nonneg
    (w : Config → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ c, ‖(w c : ℂ)‖ ≤ C) (hnonneg : ∀ c, 0 ≤ w c) :
    (completedBoundedDiagonalOperator (fun c => (w c : ℂ)) hC hbound).IsPositive := by
  let T : CompletedFock Config →L[ℂ] CompletedFock Config :=
    completedBoundedDiagonalOperator (fun c => (w c : ℂ)) hC hbound
  have hcoord (x : CompletedFock Config) (c : Config) :
      T x c = (w c : ℂ) * x c := by
    exact completedBoundedDiagonalOperator_apply
      (fun c => (w c : ℂ)) hC hbound x c
  change T.IsPositive
  rw [ContinuousLinearMap.isPositive_def]
  constructor
  · intro x y
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    apply tsum_congr
    intro c
    calc
      inner ℂ (T x c) (y c) =
          inner ℂ ((w c : ℂ) * x c) (y c) := by
            exact congrArg (fun z : ℂ => inner ℂ z (y c)) (hcoord x c)
      _ = inner ℂ (x c) ((w c : ℂ) * y c) := by
        simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
        ac_rfl
      _ = inner ℂ (x c) (T y c) := by
        exact congrArg (fun z : ℂ => inner ℂ (x c) z) (hcoord y c).symm
  · intro x
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, lp.inner_eq_tsum]
    have hs : Summable fun c : Config => inner ℂ (T x c) (x c) :=
      lp.summable_inner (T x) x
    have hre :
        RCLike.re (∑' c : Config, inner ℂ (T x c) (x c)) =
          ∑' c : Config, RCLike.re (inner ℂ (T x c) (x c)) := by
      exact RCLike.reCLM.map_tsum hs
    rw [hre]
    apply tsum_nonneg
    intro c
    rw [hcoord x c]
    have hscalar :
        RCLike.re (inner ℂ ((w c : ℂ) * x c) (x c)) =
          w c * ‖x c‖ ^ 2 := by
      calc
        RCLike.re (inner ℂ ((w c : ℂ) * x c) (x c)) =
            RCLike.re ((w c : ℂ) * (x c * (starRingEnd ℂ) (x c))) := by
              simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
              congr 1
              ac_rfl
        _ = w c * ‖x c‖ ^ 2 := by
          rw [RCLike.mul_conj, RCLike.re_eq_complex_re]
          simp
    rw [hscalar]
    exact mul_nonneg (hnonneg c) (sq_nonneg ‖x c‖)

/-- The maximal diagonal operator is densely defined for every scalar configuration weight. -/
theorem completedDiagonalOperator_denseDomain (w : Config → ℂ) :
    Dense (((completedDiagonalOperator w).domain : Submodule ℂ (CompletedFock Config)) :
      Set (CompletedFock Config)) := by
  apply Dense.mono ?_ algebraicToCompleted_denseRange
  rintro _ ⟨x, rfl⟩
  exact algebraicToCompleted_mem_completedDiagonalDomain w x

private theorem mem_completedDiagonalOperator_graph_iff (w : Config → ℂ)
    (z : CompletedFock Config × CompletedFock Config) :
    z ∈ (completedDiagonalOperator w).graph ↔
      ∀ c : Config, z.2 c = w c * z.1 c := by
  constructor
  · intro hz c
    rw [LinearPMap.mem_graph_iff] at hz
    obtain ⟨x, hx, hfx⟩ := hz
    calc
      z.2 c = (completedDiagonalOperator w x) c :=
        (congrArg (fun ψ : CompletedFock Config => ψ c) hfx).symm
      _ = w c * (x : CompletedFock Config) c := completedDiagonalOperator_apply w x c
      _ = w c * z.1 c := by rw [hx]
  · intro hz
    have hdomain : z.1 ∈ completedDiagonalDomain w := by
      rw [mem_completedDiagonalDomain_iff]
      convert (lp.memℓp z.2) using 1
      funext c
      exact (hz c).symm
    rw [LinearPMap.mem_graph_iff]
    refine ⟨⟨z.1, hdomain⟩, rfl, ?_⟩
    ext c
    rw [completedDiagonalOperator_apply]
    exact (hz c).symm

/-- A maximal diagonal multiplication operator is closed for an arbitrary complex weight. -/
theorem completedDiagonalOperator_isClosed (w : Config → ℂ) :
    (completedDiagonalOperator w).IsClosed := by
  rw [LinearPMap.IsClosed]
  have hgraph :
      ((completedDiagonalOperator w).graph :
        Set (CompletedFock Config × CompletedFock Config)) =
        ⋂ c : Config,
          {z : CompletedFock Config × CompletedFock Config |
            z.2 c = w c * z.1 c} := by
    ext z
    rw [Set.mem_iInter]
    exact mem_completedDiagonalOperator_graph_iff w z
  rw [hgraph]
  apply isClosed_iInter
  intro c
  apply isClosed_eq
  · exact (lp.evalCLM ℂ (fun _ : Config => ℂ) 2 c).continuous.comp continuous_snd
  · exact continuous_const.mul
      ((lp.evalCLM ℂ (fun _ : Config => ℂ) 2 c).continuous.comp continuous_fst)

private theorem completedDiagonalOperator_isFormalAdjoint_conj (w : Config → ℂ) :
    (completedDiagonalOperator w).IsFormalAdjoint
      (completedDiagonalOperator fun c => star (w c)) := by
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro c
  rw [completedDiagonalOperator_apply, completedDiagonalOperator_apply]
  simp [mul_assoc, mul_left_comm]

private theorem completedDiagonalOperator_conj_le_adjoint (w : Config → ℂ) :
    completedDiagonalOperator (fun c => star (w c)) ≤
      (completedDiagonalOperator w).adjoint :=
  (completedDiagonalOperator_isFormalAdjoint_conj w).le_adjoint
    (completedDiagonalOperator_denseDomain w)

private theorem completedDiagonalOperator_adjoint_apply (w : Config → ℂ)
    (y : (completedDiagonalOperator w).adjoint.domain) (c : Config) :
    (completedDiagonalOperator w).adjoint y c =
      star (w c) * (y : CompletedFock Config) c := by
  let e : (completedDiagonalOperator w).domain :=
    ⟨completedBasisState c, completedBasisState_mem_completedDiagonalDomain w c⟩
  have h := ((completedDiagonalOperator w).adjoint_isFormalAdjoint
    (completedDiagonalOperator_denseDomain w)).symm e y
  have he : completedDiagonalOperator w e = w c • completedBasisState c := by
    exact completedDiagonalOperator_basisState w c
  rw [he] at h
  change inner ℂ (w c • completedBasisState c) (y : CompletedFock Config) =
    inner ℂ (completedBasisState c) ((completedDiagonalOperator w).adjoint y) at h
  rw [inner_smul_left, inner_completedBasisState_left, inner_completedBasisState_left] at h
  exact h.symm

private theorem completedDiagonalOperator_adjoint_domain_le_conj (w : Config → ℂ) :
    (completedDiagonalOperator w).adjoint.domain ≤
      completedDiagonalDomain (fun c => star (w c)) := by
  intro y hy
  rw [mem_completedDiagonalDomain_iff]
  let y' : (completedDiagonalOperator w).adjoint.domain := ⟨y, hy⟩
  convert (lp.memℓp ((completedDiagonalOperator w).adjoint y')) using 1
  funext c
  exact (completedDiagonalOperator_adjoint_apply w y' c).symm

private theorem completedDiagonalOperator_adjoint_le_conj (w : Config → ℂ) :
    (completedDiagonalOperator w).adjoint ≤
      completedDiagonalOperator (fun c => star (w c)) := by
  refine ⟨completedDiagonalOperator_adjoint_domain_le_conj w, ?_⟩
  intro x y hxy
  ext c
  rw [completedDiagonalOperator_adjoint_apply, completedDiagonalOperator_apply]
  change star (w c) * (x : CompletedFock Config) c =
    star (w c) * (y : CompletedFock Config) c
  rw [hxy]

/-- The adjoint of a maximal diagonal multiplication operator is exactly multiplication by the
complex-conjugated weight on its maximal weighted `ℓ²` domain. -/
theorem completedDiagonalOperator_adjoint_eq (w : Config → ℂ) :
    (completedDiagonalOperator w).adjoint =
      completedDiagonalOperator (fun c => star (w c)) :=
  le_antisymm (completedDiagonalOperator_adjoint_le_conj w)
    (completedDiagonalOperator_conj_le_adjoint w)

/-- A diagonal operator whose weights are fixed by complex conjugation is formally symmetric. -/
theorem completedDiagonalOperator_isFormalAdjoint_self (w : Config → ℂ)
    (hw : ∀ c, star (w c) = w c) :
    (completedDiagonalOperator w).IsFormalAdjoint (completedDiagonalOperator w) := by
  have h := completedDiagonalOperator_isFormalAdjoint_conj w
  have hwfun : (fun c => star (w c)) = w := funext hw
  rw [hwfun] at h
  exact h

/-- A maximal diagonal operator with conjugation-fixed weights is self-adjoint. -/
theorem completedDiagonalOperator_isSelfAdjoint_of_star (w : Config → ℂ)
    (hw : ∀ c, star (w c) = w c) :
    IsSelfAdjoint (completedDiagonalOperator w) := by
  rw [LinearPMap.isSelfAdjoint_def, completedDiagonalOperator_adjoint_eq]
  congr 1
  funext c
  exact hw c

end
end Common
end SecondQuantization
