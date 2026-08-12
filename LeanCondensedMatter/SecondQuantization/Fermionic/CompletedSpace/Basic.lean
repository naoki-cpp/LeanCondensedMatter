import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.NumberOperator
import Mathlib.Analysis.InnerProductSpace.l2Space

set_option linter.style.header false

/-!
# Completed fermionic Fock space

This file starts the completed-space vertical slice tracked by issue #440. For a mode type `Mode`,
the completed fermionic Fock space is the Hilbert space of square-summable complex amplitudes on
finite occupation configurations:

```text
ℓ²(Fermionic.Occupation Mode, ℂ) = ℓ²(Finset Mode, ℂ).
```

The existing algebraic Fock space consists of finitely supported amplitudes on the same occupation
basis. Its coordinate-preserving map into the completed space is injective and has dense range.

As the first completed operator, this file defines the single-mode occupation projection. It is a
bounded continuous linear map of norm at most one and agrees with the existing algebraic number
operator on the full algebraic core. Creation, annihilation, free Hamiltonians with unbounded
one-particle energies, and their domains are deliberately not bundled as continuous linear maps
here; those require separate boundedness or `LinearPMap` domain proofs.
-/

namespace SecondQuantization
namespace Fermionic

open scoped ENNReal

noncomputable section

/-- The completed fermionic Fock space: square-summable amplitudes on finite occupation states. -/
abbrev CompletedFockSpace (Mode : Type*) :=
  lp (fun _ : Occupation Mode => ℂ) 2

variable {Mode : Type*}

/-- The canonical occupation-basis vector in completed fermionic Fock space. -/
noncomputable def completedBasisState (n : Occupation Mode) : CompletedFockSpace Mode := by
  classical
  exact lp.single 2 n 1

/-- The coordinate-preserving inclusion of algebraic fermionic Fock space into its `ℓ²` completion. -/
noncomputable def algebraicToCompleted :
    OccupationFock Mode →ₗ[ℂ] CompletedFockSpace Mode where
  toFun x :=
    ⟨fun n => x n, (memℓp_zero x.hasFiniteSupport).of_exponent_ge zero_le⟩
  map_add' x y := by
    apply lp.ext
    funext n
    rfl
  map_smul' c x := by
    apply lp.ext
    funext n
    rfl

@[simp]
theorem algebraicToCompleted_apply (x : OccupationFock Mode) (n : Occupation Mode) :
    algebraicToCompleted x n = x n :=
  rfl

@[simp]
theorem algebraicToCompleted_basisState (n : Occupation Mode) :
    algebraicToCompleted (basisState n) = completedBasisState n := by
  classical
  apply lp.ext
  funext m
  by_cases h : m = n
  · subst m
    simp [algebraicToCompleted, basisState, Common.basisState, completedBasisState,
      Finsupp.single_apply, lp.single_apply]
  · have hnm : n ≠ m := Ne.symm h
    simp [algebraicToCompleted, basisState, Common.basisState, completedBasisState,
      Finsupp.single_apply, lp.single_apply, h, hnm, Pi.single_eq_of_ne]

/-- The algebraic-to-completed inclusion loses no finite-support vector. -/
theorem algebraicToCompleted_injective :
    Function.Injective
      (algebraicToCompleted : OccupationFock Mode → CompletedFockSpace Mode) := by
  intro x y hxy
  apply Finsupp.ext
  intro n
  exact congrArg (fun z : CompletedFockSpace Mode => z n) hxy

/-- Finite-support fermionic Fock vectors are dense in the completed `ℓ²` space. -/
theorem algebraicToCompleted_denseRange :
    DenseRange
      (algebraicToCompleted : OccupationFock Mode → CompletedFockSpace Mode) := by
  classical
  intro ψ
  refine mem_closure_of_tendsto (lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) ψ) ?_
  filter_upwards [] with s
  refine ⟨s.sum (fun n => ψ n • basisState n), ?_⟩
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [map_smul, algebraicToCompleted_basisState]
  apply lp.ext
  funext m
  by_cases h : m = n
  · subst m
    simp [completedBasisState, lp.single_apply]
  · simp [completedBasisState, lp.single_apply, h, Pi.single_eq_of_ne]

variable [LinearOrder Mode]

/-- The underlying linear map of the completed single-mode occupation projection. -/
noncomputable def completedNumberOperatorLinear (i : Mode) :
    CompletedFockSpace Mode →ₗ[ℂ] CompletedFockSpace Mode where
  toFun ψ :=
    ⟨fun n => if i ∈ n then ψ n else 0,
      (lp.memℓp ψ).mono' fun n => by
        by_cases h : i ∈ n <;> simp [h]⟩
  map_add' ψ φ := by
    apply lp.ext
    funext n
    by_cases h : i ∈ n <;> simp [h]
  map_smul' c ψ := by
    apply lp.ext
    funext n
    by_cases h : i ∈ n <;> simp [h]

@[simp]
theorem completedNumberOperatorLinear_apply (i : Mode) (ψ : CompletedFockSpace Mode)
    (n : Occupation Mode) :
    completedNumberOperatorLinear i ψ n = if i ∈ n then ψ n else 0 :=
  rfl

/-- The completed single-mode number operator. It is the orthogonal coordinate projection onto
occupation configurations containing `i`, hence has operator norm at most one. -/
noncomputable def completedNumberOperator (i : Mode) :
    CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode :=
  (completedNumberOperatorLinear i).mkContinuous 1 fun ψ => by
    simpa only [one_mul] using
      lp.norm_mono (p := (2 : ℝ≥0∞)) (by norm_num)
        (x := completedNumberOperatorLinear i ψ) (y := ψ) (fun n => by
          by_cases h : i ∈ n <;> simp [h])

@[simp]
theorem completedNumberOperator_apply (i : Mode) (ψ : CompletedFockSpace Mode)
    (n : Occupation Mode) :
    completedNumberOperator i ψ n = if i ∈ n then ψ n else 0 :=
  rfl

/-- The completed number operator has the same occupation-basis eigenvalue equation as the
algebraic number operator. -/
@[simp]
theorem completedNumberOperator_basisState (i : Mode) (n : Occupation Mode) :
    completedNumberOperator i (completedBasisState n) =
      if i ∈ n then completedBasisState n else 0 := by
  classical
  apply lp.ext
  funext m
  by_cases hi : i ∈ n <;> by_cases hm : m = n <;>
    simp [completedBasisState, completedNumberOperator_apply, hi, hm, lp.single_apply]

/-- The completed single-mode number operator agrees with the algebraic number operator on the
whole finite-support core, not only on individual basis states. -/
theorem completedNumberOperator_comp_algebraicToCompleted (i : Mode) :
    (completedNumberOperator i).toLinearMap.comp algebraicToCompleted =
      algebraicToCompleted.comp (numberOperator i) := by
  apply Finsupp.lhom_ext
  intro n c
  have hc : (Finsupp.single n c : OccupationFock Mode) = c • basisState n :=
    (Finsupp.smul_single_one n c).symm
  rw [hc]
  simp only [LinearMap.comp_apply, map_smul]
  by_cases hi : i ∈ n <;>
    simp [numberOperator_basisState, hi]

end
end Fermionic
end SecondQuantization
