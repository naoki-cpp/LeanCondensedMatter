import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.Hamiltonian
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.CanonicalAnticommutationRelations
import Mathlib.LinearAlgebra.LinearPMap

set_option linter.style.header false

/-!
# Diagonal unbounded operators on completed fermionic Fock space

A diagonal occupation operator with weight `w : Occupation Mode → ℂ` need not be bounded on the
completed `ℓ²` Fock space. Its natural domain consists exactly of vectors `ψ` for which the
weighted coordinate function `n ↦ w n * ψ n` is again square summable.

This file packages that operator as a `LinearPMap`. It deliberately stops at the domain-carrying
linear operator: closedness, adjoints, and self-adjointness are later analytic theorems rather than
part of the definition.
-/

namespace SecondQuantization
namespace Fermionic

open scoped ENNReal

noncomputable section

variable {Mode : Type*}

/-- Raw coordinate multiplication by an occupation-dependent scalar weight. The codomain is the
ambient `PreLp` function space because multiplication by an unbounded weight need not preserve
`ℓ²`. -/
noncomputable def completedDiagonalCoordinates (w : Occupation Mode → ℂ) :
    CompletedFockSpace Mode →ₗ[ℂ] PreLp (fun _ : Occupation Mode => ℂ) where
  toFun ψ := fun n => w n * ψ n
  map_add' ψ φ := by
    funext n
    change w n * (ψ n + φ n) = w n * ψ n + w n * φ n
    ring
  map_smul' c ψ := by
    funext n
    change w n * (c * ψ n) = c * (w n * ψ n)
    ring

@[simp]
theorem completedDiagonalCoordinates_apply (w : Occupation Mode → ℂ)
    (ψ : CompletedFockSpace Mode) (n : Occupation Mode) :
    completedDiagonalCoordinates w ψ n = w n * ψ n :=
  rfl

/-- Natural domain of a diagonal occupation operator: the weighted amplitudes must remain in
`ℓ²`. Defining it as a preimage of `lpSubmodule` makes linearity of the domain structural rather
than a separate summability proof. -/
noncomputable def completedDiagonalDomain (w : Occupation Mode → ℂ) :
    Submodule ℂ (CompletedFockSpace Mode) :=
  (lpSubmodule ℂ (fun _ : Occupation Mode => ℂ) 2).comap (completedDiagonalCoordinates w)

@[simp]
theorem mem_completedDiagonalDomain_iff (w : Occupation Mode → ℂ)
    (ψ : CompletedFockSpace Mode) :
    ψ ∈ completedDiagonalDomain w ↔ Memℓp (fun n => w n * ψ n) 2 := by
  rfl

/-- The maximal diagonal partial linear map associated to `w` on the explicit weighted `ℓ²`
domain. -/
noncomputable def completedDiagonalOperator (w : Occupation Mode → ℂ) :
    CompletedFockSpace Mode →ₗ.[ℂ] CompletedFockSpace Mode where
  domain := completedDiagonalDomain w
  toFun :=
    { toFun := fun ψ =>
        ⟨fun n => w n * (ψ : CompletedFockSpace Mode) n,
          (mem_completedDiagonalDomain_iff w (ψ : CompletedFockSpace Mode)).mp ψ.2⟩
      map_add' ψ φ := by
        apply lp.ext
        funext n
        change w n * ((ψ : CompletedFockSpace Mode) n + (φ : CompletedFockSpace Mode) n) =
          w n * (ψ : CompletedFockSpace Mode) n + w n * (φ : CompletedFockSpace Mode) n
        ring
      map_smul' c ψ := by
        apply lp.ext
        funext n
        change w n * (c * (ψ : CompletedFockSpace Mode) n) =
          c * (w n * (ψ : CompletedFockSpace Mode) n)
        ring }

@[simp]
theorem completedDiagonalOperator_apply (w : Occupation Mode → ℂ)
    (ψ : (completedDiagonalOperator w).domain) (n : Occupation Mode) :
    completedDiagonalOperator w ψ n = w n * (ψ : CompletedFockSpace Mode) n :=
  rfl

@[simp]
theorem completedDiagonalOperator_toFun_apply (w : Occupation Mode → ℂ)
    (ψ : (completedDiagonalOperator w).domain) (n : Occupation Mode) :
    (completedDiagonalOperator w).toFun ψ n = w n * (ψ : CompletedFockSpace Mode) n :=
  rfl

/-- Every finite-support algebraic Fock vector belongs to every weighted diagonal domain. -/
theorem algebraicToCompleted_mem_completedDiagonalDomain (w : Occupation Mode → ℂ)
    (x : OccupationFock Mode) :
    algebraicToCompleted x ∈ completedDiagonalDomain w := by
  rw [mem_completedDiagonalDomain_iff]
  apply (memℓp_zero ?_).of_exponent_ge zero_le
  refine x.hasFiniteSupport.subset ?_
  intro n hn
  simp only [Function.mem_support] at hn ⊢
  intro hx
  apply hn
  simp [algebraicToCompleted_apply, hx]

/-- The algebraic core, regarded as a linear map into the weighted diagonal domain. -/
noncomputable def algebraicToCompletedDiagonalDomain (w : Occupation Mode → ℂ) :
    OccupationFock Mode →ₗ[ℂ] completedDiagonalDomain w where
  toFun x := ⟨algebraicToCompleted x, algebraicToCompleted_mem_completedDiagonalDomain w x⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add algebraicToCompleted x y
  map_smul' c x := by
    apply Subtype.ext
    exact map_smul algebraicToCompleted c x

@[simp]
theorem algebraicToCompletedDiagonalDomain_coe (w : Occupation Mode → ℂ)
    (x : OccupationFock Mode) :
    ((algebraicToCompletedDiagonalDomain w x : completedDiagonalDomain w) :
      CompletedFockSpace Mode) = algebraicToCompleted x :=
  rfl

@[simp]
theorem algebraicToCompletedDiagonalDomain_apply (w : Occupation Mode → ℂ)
    (x : OccupationFock Mode) (n : Occupation Mode) :
    (((algebraicToCompletedDiagonalDomain w x : completedDiagonalDomain w) :
      CompletedFockSpace Mode) n) = x n :=
  rfl

theorem algebraicToCompletedDiagonalDomain_basisState (w : Occupation Mode → ℂ)
    (n : Occupation Mode) :
    ((algebraicToCompletedDiagonalDomain w (basisState n) : completedDiagonalDomain w) :
      CompletedFockSpace Mode) = completedBasisState n := by
  exact algebraicToCompleted_basisState n

/-- Basis vectors lie in every diagonal domain. -/
theorem completedBasisState_mem_completedDiagonalDomain (w : Occupation Mode → ℂ)
    (n : Occupation Mode) :
    completedBasisState n ∈ completedDiagonalDomain w := by
  rw [← algebraicToCompleted_basisState]
  exact algebraicToCompleted_mem_completedDiagonalDomain w (basisState n)

/-- The expected diagonal eigenvalue equation on the completed occupation basis. -/
@[simp]
theorem completedDiagonalOperator_basisState (w : Occupation Mode → ℂ)
    (n : Occupation Mode) :
    completedDiagonalOperator w
        ⟨completedBasisState n, completedBasisState_mem_completedDiagonalDomain w n⟩ =
      w n • completedBasisState n := by
  classical
  apply lp.ext
  funext m
  rw [completedDiagonalOperator_apply]
  by_cases h : m = n
  · subst m
    simp
  · simp [completedBasisState_apply_of_ne h]

/-- On the whole finite-support core, the completed partial operator agrees with the existing
algebraic diagonal operator. -/
theorem completedDiagonalOperator_comp_algebraicCore (w : Occupation Mode → ℂ) :
    (completedDiagonalOperator w).toFun.comp (algebraicToCompletedDiagonalDomain w) =
      algebraicToCompleted.comp (Common.diagonalOperator w) := by
  apply Finsupp.lhom_ext
  intro n c
  have hc : (Finsupp.single n c : OccupationFock Mode) = c • basisState n :=
    (Finsupp.smul_single_one n c).symm
  rw [hc]
  simp only [LinearMap.comp_apply, map_smul]
  have hdomain :
      algebraicToCompletedDiagonalDomain w (basisState n) =
        ⟨completedBasisState n, completedBasisState_mem_completedDiagonalDomain w n⟩ := by
    apply Subtype.ext
    exact algebraicToCompleted_basisState n
  have hleft :
      (completedDiagonalOperator w).toFun
          (algebraicToCompletedDiagonalDomain w (basisState n)) =
        w n • completedBasisState n := by
    rw [hdomain]
    change completedDiagonalOperator w
        ⟨completedBasisState n, completedBasisState_mem_completedDiagonalDomain w n⟩ =
      w n • completedBasisState n
    exact completedDiagonalOperator_basisState w n
  have hright :
      algebraicToCompleted (Common.diagonalOperator w (basisState n)) =
        w n • completedBasisState n := by
    change algebraicToCompleted (Common.diagonalOperator w (Common.basisState n)) =
      w n • completedBasisState n
    rw [Common.diagonalOperator_basisState, map_smul]
    congr 1
    simpa [basisState] using algebraicToCompleted_basisState (Mode := Mode) n
  exact congrArg (fun y : CompletedFockSpace Mode => c • y) (hleft.trans hright.symm)

/-! ## Free Hamiltonian and total particle number -/

/-- Occupation energy used by the free Hamiltonian. -/
noncomputable def freeHamiltonianWeight (ε : Mode → ℝ) (n : Occupation Mode) : ℂ :=
  ∑ i ∈ n, (ε i : ℂ)

/-- Natural weighted `ℓ²` domain of the free Hamiltonian. -/
noncomputable def completedFreeHamiltonianDomain (ε : Mode → ℝ) :
    Submodule ℂ (CompletedFockSpace Mode) :=
  completedDiagonalDomain (freeHamiltonianWeight ε)

/-- Free Hamiltonian on completed Fock space, with its natural weighted square-summability domain. -/
noncomputable def completedFreeHamiltonian (ε : Mode → ℝ) :
    CompletedFockSpace Mode →ₗ.[ℂ] CompletedFockSpace Mode :=
  completedDiagonalOperator (freeHamiltonianWeight ε)

/-- Natural domain of the total number operator on the completed Fock space. -/
noncomputable def completedTotalNumberDomain :
    Submodule ℂ (CompletedFockSpace Mode) :=
  completedDiagonalDomain fun n : Occupation Mode => (particleNumber n : ℂ)

/-- Total particle-number operator as an unbounded diagonal partial linear map. -/
noncomputable def completedTotalNumberOperator :
    CompletedFockSpace Mode →ₗ.[ℂ] CompletedFockSpace Mode :=
  completedDiagonalOperator fun n : Occupation Mode => (particleNumber n : ℂ)

/-- The completed free Hamiltonian extends the existing algebraic free Hamiltonian on the entire
finite-support core. -/
theorem completedFreeHamiltonian_comp_algebraicCore (ε : Mode → ℝ) :
    (completedFreeHamiltonian ε).toFun.comp
        (algebraicToCompletedDiagonalDomain (freeHamiltonianWeight ε)) =
      algebraicToCompleted.comp (freeHamiltonian ε) := by
  change
    (completedDiagonalOperator (freeHamiltonianWeight ε)).toFun.comp
        (algebraicToCompletedDiagonalDomain (freeHamiltonianWeight ε)) =
      algebraicToCompleted.comp (Common.diagonalOperator (freeHamiltonianWeight ε))
  exact completedDiagonalOperator_comp_algebraicCore (freeHamiltonianWeight ε)

/-- The completed total-number operator extends the algebraic total-number operator on the entire
finite-support core. -/
theorem completedTotalNumberOperator_comp_algebraicCore :
    completedTotalNumberOperator.toFun.comp
        (algebraicToCompletedDiagonalDomain
          (fun n : Occupation Mode => (particleNumber n : ℂ))) =
      algebraicToCompleted.comp (totalNumberOperator : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) := by
  change
    (completedDiagonalOperator (fun n : Occupation Mode => (particleNumber n : ℂ))).toFun.comp
        (algebraicToCompletedDiagonalDomain
          (fun n : Occupation Mode => (particleNumber n : ℂ))) =
      algebraicToCompleted.comp
        (Common.diagonalOperator fun n : Occupation Mode => (particleNumber n : ℂ))
  exact completedDiagonalOperator_comp_algebraicCore
    (fun n : Occupation Mode => (particleNumber n : ℂ))

end
end Fermionic
end SecondQuantization
