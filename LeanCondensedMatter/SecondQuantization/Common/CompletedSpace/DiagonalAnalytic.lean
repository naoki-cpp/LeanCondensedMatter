import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.Diagonal
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
      have hout := lp.memℓp z.2
      convert hout using 1
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
  have hout := lp.memℓp ((completedDiagonalOperator w).adjoint y')
  convert hout using 1
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
