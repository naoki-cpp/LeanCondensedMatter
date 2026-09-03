import LeanCondensedMatter.SecondQuantization.Common.Algebra.AlgebraicFock
import Mathlib.Analysis.InnerProductSpace.l2Space

set_option linter.style.header false

/-!
# Completed Fock space over an arbitrary configuration type

This module owns the statistics-independent Hilbert completion of an algebraic Fock space.
For an arbitrary configuration type `Config`, the completed space is the square-summable complex
amplitude space `ℓ²(Config, ℂ)`. The canonical finite-support algebraic Fock space embeds
coordinatewise with dense range.

Statistics-specific layers should specialize `Config` to their own occupation type and keep only
occupation/sign/operator semantics locally.
-/

namespace SecondQuantization
namespace Common

open scoped ENNReal

noncomputable section

/-- The completed Fock space over a configuration type: square-summable complex amplitudes. -/
abbrev CompletedFock (Config : Type*) :=
  lp (fun _ : Config => ℂ) 2

variable {Config : Type*}

/-- The canonical configuration-basis vector in completed Fock space. -/
noncomputable def completedBasisState (c : Config) : CompletedFock Config := by
  classical
  exact lp.single 2 c 1

/-- The canonical configuration Hilbert basis of completed Fock space. -/
noncomputable def completedHilbertBasis :
    HilbertBasis Config ℂ (CompletedFock Config) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ (CompletedFock Config))

@[simp]
theorem completedHilbertBasis_apply (c : Config) :
    completedHilbertBasis (Config := Config) c = completedBasisState c := by
  classical
  simpa [completedHilbertBasis, completedBasisState] using
    (completedHilbertBasis (Config := Config)).repr_self c

/-- Inner product with a completed basis vector in the first slot evaluates the corresponding
coordinate. -/
@[simp]
theorem inner_completedBasisState_left (c : Config) (ψ : CompletedFock Config) :
    inner ℂ (completedBasisState c) ψ = ψ c := by
  classical
  unfold completedBasisState
  simpa using lp.inner_single_left (𝕜 := ℂ) c (1 : ℂ) ψ

@[simp]
theorem completedBasisState_apply_self (c : Config) :
    completedBasisState c c = 1 := by
  classical
  simp [completedBasisState, lp.single_apply]

@[simp]
theorem completedBasisState_apply_of_ne {c d : Config} (h : c ≠ d) :
    completedBasisState d c = 0 := by
  classical
  simp [completedBasisState, lp.single_apply, h, Pi.single_eq_of_ne]

/-- The coordinate-preserving inclusion of algebraic Fock space into its `ℓ²` completion. -/
noncomputable def algebraicToCompleted :
    AlgebraicFock Config →ₗ[ℂ] CompletedFock Config where
  toFun x :=
    ⟨fun c => x c, (memℓp_zero x.hasFiniteSupport).of_exponent_ge zero_le⟩
  map_add' x y := by
    ext c
    rfl
  map_smul' a x := by
    ext c
    rfl

@[simp]
theorem algebraicToCompleted_apply (x : AlgebraicFock Config) (c : Config) :
    algebraicToCompleted x c = x c :=
  rfl

@[simp]
theorem algebraicToCompleted_basisState (c : Config) :
    algebraicToCompleted (basisState c) = completedBasisState c := by
  classical
  ext d
  by_cases h : d = c
  · subst d
    simp [algebraicToCompleted, basisState, completedBasisState,
      Finsupp.single_apply, lp.single_apply]
  · have hcd : c ≠ d := Ne.symm h
    simp [algebraicToCompleted, basisState, completedBasisState,
      Finsupp.single_apply, lp.single_apply, h, hcd, Pi.single_eq_of_ne]

/-- The algebraic-to-completed inclusion loses no finite-support vector. -/
theorem algebraicToCompleted_injective :
    Function.Injective
      (algebraicToCompleted : AlgebraicFock Config → CompletedFock Config) := by
  intro x y hxy
  apply Finsupp.ext
  intro c
  exact congrArg (fun z : CompletedFock Config => z c) hxy

/-- Finite-support algebraic Fock vectors are dense in the completed `ℓ²` space. -/
theorem algebraicToCompleted_denseRange :
    DenseRange
      (algebraicToCompleted : AlgebraicFock Config → CompletedFock Config) := by
  classical
  intro ψ
  refine mem_closure_of_tendsto (lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) ψ) ?_
  filter_upwards [] with s
  refine ⟨s.sum (fun c => ψ c • basisState c), ?_⟩
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro c _hc
  rw [map_smul, algebraicToCompleted_basisState]
  ext d
  by_cases h : d = c
  · subst d
    simp [completedBasisState, lp.single_apply]
  · simp [completedBasisState, lp.single_apply, h, Pi.single_eq_of_ne]

/-- Continuous linear maps out of completed Fock space are determined by their values on the dense
finite-support algebraic core. -/
theorem continuousLinearMap_ext_algebraicCore
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A B : CompletedFock Config →L[ℂ] E}
    (h : ∀ x : AlgebraicFock Config, A (algebraicToCompleted x) = B (algebraicToCompleted x)) :
    A = B := by
  apply DFunLike.ext'
  exact (map_continuous A).ext_on algebraicToCompleted_denseRange (map_continuous B) <| by
    rintro _ ⟨x, rfl⟩
    exact h x

/-- Continuous linear maps out of completed Fock space are determined by their values on the
canonical completed basis. -/
theorem continuousLinearMap_ext_completedBasis
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A B : CompletedFock Config →L[ℂ] E}
    (h : ∀ c : Config, A (completedBasisState c) = B (completedBasisState c)) :
    A = B := by
  apply continuousLinearMap_ext_algebraicCore
  intro x
  have hcore :
      A.toLinearMap.comp algebraicToCompleted =
        B.toLinearMap.comp algebraicToCompleted := by
    apply Finsupp.lhom_ext
    intro c a
    have ha : (Finsupp.single c a : AlgebraicFock Config) = a • basisState c :=
      (Finsupp.smul_single_one c a).symm
    rw [ha]
    simp only [LinearMap.comp_apply, map_smul, algebraicToCompleted_basisState]
    exact congrArg (fun y : E => a • y) (h c)
  exact congrArg (fun f : AlgebraicFock Config →ₗ[ℂ] E => f x) hcore

end
end Common
end SecondQuantization
