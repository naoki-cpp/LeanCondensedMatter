import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.Basic
import Mathlib.LinearAlgebra.LinearPMap

set_option linter.style.header false

/-!
# Diagonal unbounded operators on generic completed Fock space

A scalar weight `w : Config → ℂ` defines coordinatewise multiplication on the generic completed
Fock space. For an unbounded weight, the natural maximal domain consists of vectors whose weighted
coordinates remain square summable. This file owns that statistics-independent domain and the
associated maximal `LinearPMap`.
-/

namespace SecondQuantization
namespace Common

open scoped ENNReal

noncomputable section

variable {Config : Type*}

private noncomputable def completedDiagonalCoordinates (w : Config → ℂ) :
    CompletedFock Config →ₗ[ℂ] PreLp (fun _ : Config => ℂ) where
  toFun ψ := fun c => w c * ψ c
  map_add' ψ φ := by
    funext c
    change w c * (ψ c + φ c) = w c * ψ c + w c * φ c
    ring
  map_smul' a ψ := by
    funext c
    change w c * (a * ψ c) = a * (w c * ψ c)
    ring

/-- Maximal weighted `ℓ²` domain associated with a scalar configuration weight. -/
noncomputable def completedDiagonalDomain (w : Config → ℂ) :
    Submodule ℂ (CompletedFock Config) :=
  (lpSubmodule ℂ (fun _ : Config => ℂ) 2).comap (completedDiagonalCoordinates w)

@[simp]
theorem mem_completedDiagonalDomain_iff (w : Config → ℂ) (ψ : CompletedFock Config) :
    ψ ∈ completedDiagonalDomain w ↔ Memℓp (fun c => w c * ψ c) 2 := by
  rfl

/-- Maximal diagonal partial linear map associated with `w`. -/
noncomputable def completedDiagonalOperator (w : Config → ℂ) :
    CompletedFock Config →ₗ.[ℂ] CompletedFock Config where
  domain := completedDiagonalDomain w
  toFun :=
    { toFun := fun ψ =>
        ⟨fun c => w c * (ψ : CompletedFock Config) c,
          (mem_completedDiagonalDomain_iff w (ψ : CompletedFock Config)).mp ψ.2⟩
      map_add' ψ φ := by
        ext c
        change w c * ((ψ : CompletedFock Config) c + (φ : CompletedFock Config) c) =
          w c * (ψ : CompletedFock Config) c + w c * (φ : CompletedFock Config) c
        ring
      map_smul' a ψ := by
        ext c
        change w c * (a * (ψ : CompletedFock Config) c) =
          a * (w c * (ψ : CompletedFock Config) c)
        ring }

@[simp]
theorem completedDiagonalOperator_apply (w : Config → ℂ)
    (ψ : (completedDiagonalOperator w).domain) (c : Config) :
    completedDiagonalOperator w ψ c = w c * (ψ : CompletedFock Config) c := by
  rfl

/-- Membership in a diagonal weighted `ℓ²` domain is stable under adding a finite scalar constant
to the weight. -/
theorem mem_completedDiagonalDomain_add_const
    (w : Config → ℂ) (c : ℂ) {ψ : CompletedFock Config}
    (hψ : ψ ∈ completedDiagonalDomain w) :
    ψ ∈ completedDiagonalDomain (fun n => w n + c) := by
  rw [mem_completedDiagonalDomain_iff]
  let x : (completedDiagonalOperator w).domain := ⟨ψ, hψ⟩
  have hout := lp.memℓp (completedDiagonalOperator w x + c • ψ)
  have hfun :
      (fun n : Config => (w n + c) * ψ n) =
        (fun n : Config => (completedDiagonalOperator w x + c • ψ) n) := by
    funext n
    change (w n + c) * ψ n = w n * ψ n + c * ψ n
    ring
  rw [hfun]
  exact hout

/-- Every finite-support algebraic Fock vector belongs to every weighted diagonal domain. -/
theorem algebraicToCompleted_mem_completedDiagonalDomain (w : Config → ℂ)
    (x : AlgebraicFock Config) :
    algebraicToCompleted x ∈ completedDiagonalDomain w := by
  rw [mem_completedDiagonalDomain_iff]
  apply (memℓp_zero ?_).of_exponent_ge zero_le
  refine x.hasFiniteSupport.subset ?_
  intro c hc
  simp only [Function.mem_support] at hc ⊢
  intro hx
  apply hc
  simp [algebraicToCompleted_apply, hx]

/-- Algebraic Fock space regarded as a linear map into a weighted diagonal domain. -/
noncomputable def algebraicToCompletedDiagonalDomain (w : Config → ℂ) :
    AlgebraicFock Config →ₗ[ℂ] completedDiagonalDomain w where
  toFun x := ⟨algebraicToCompleted x, algebraicToCompleted_mem_completedDiagonalDomain w x⟩
  map_add' x y := by
    exact Subtype.ext (map_add algebraicToCompleted x y)
  map_smul' a x := by
    exact Subtype.ext (map_smul algebraicToCompleted a x)

/-- Canonical basis vectors lie in every weighted diagonal domain. -/
theorem completedBasisState_mem_completedDiagonalDomain (w : Config → ℂ) (c : Config) :
    completedBasisState c ∈ completedDiagonalDomain w := by
  rw [← algebraicToCompleted_basisState]
  exact algebraicToCompleted_mem_completedDiagonalDomain w (basisState c)

/-- A canonical basis state is an eigenvector of the maximal diagonal operator. -/
@[simp]
theorem completedDiagonalOperator_basisState (w : Config → ℂ) (c : Config) :
    completedDiagonalOperator w
        ⟨completedBasisState c, completedBasisState_mem_completedDiagonalDomain w c⟩ =
      w c • completedBasisState c := by
  classical
  ext d
  rw [completedDiagonalOperator_apply]
  by_cases h : d = c
  · subst d
    simp
  · simp [completedBasisState_apply_of_ne h]

/-- On the finite-support core, the maximal completed diagonal operator agrees with the algebraic
configuration-diagonal operator. -/
theorem completedDiagonalOperator_comp_algebraicCore (w : Config → ℂ) :
    (completedDiagonalOperator w).toFun.comp (algebraicToCompletedDiagonalDomain w) =
      algebraicToCompleted.comp (diagonalOperator w) := by
  apply Finsupp.lhom_ext
  intro c a
  have ha : (Finsupp.single c a : AlgebraicFock Config) = a • basisState c :=
    (Finsupp.smul_single_one c a).symm
  rw [ha]
  simp only [LinearMap.comp_apply, map_smul]
  have hdomain :
      algebraicToCompletedDiagonalDomain w (basisState c) =
        ⟨completedBasisState c, completedBasisState_mem_completedDiagonalDomain w c⟩ := by
    exact Subtype.ext (algebraicToCompleted_basisState c)
  have hleft :
      (completedDiagonalOperator w).toFun
          (algebraicToCompletedDiagonalDomain w (basisState c)) =
        w c • completedBasisState c := by
    rw [hdomain]
    exact completedDiagonalOperator_basisState w c
  have hright :
      algebraicToCompleted (diagonalOperator w (basisState c)) =
        w c • completedBasisState c := by
    rw [diagonalOperator_basisState, map_smul, algebraicToCompleted_basisState]
  exact congrArg (fun y : CompletedFock Config => a • y) (hleft.trans hright.symm)

end
end Common
end SecondQuantization
