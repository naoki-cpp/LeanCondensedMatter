import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Diagonal
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Operators

set_option linter.style.header false

/-!
# Product domains for completed fermionic operators

This file starts the explicit product-domain layer for the completed fermionic representation.
The free Hamiltonian is an unbounded diagonal `LinearPMap`, so compositions with bounded ladder
operators are only formed after proving that the ladder operators preserve its maximal weighted
`ℓ²` domain.

For one fermionic mode `i`, creation and annihilation shift the occupation energy by the finite
scalar `ε i`.  The key analytic observation is therefore that adding a constant to a diagonal
weight does not shrink its domain.  Combining this with the occupation toggle gives domain
invariance of the free Hamiltonian under both bounded ladder operators.
-/

namespace SecondQuantization
namespace Fermionic

open scoped ENNReal

noncomputable section

variable {Mode : Type*} [LinearOrder Mode]

omit [LinearOrder Mode] in
/-- Membership in a diagonal weighted `ℓ²` domain is stable under adding a constant to the weight.
The proof packages the shifted weighted coordinates as the sum of the original diagonal image and
a scalar multiple of the original `ℓ²` vector. -/
theorem mem_completedDiagonalDomain_add_const
    (w : Occupation Mode → ℂ) (c : ℂ) {ψ : CompletedFockSpace Mode}
    (hψ : ψ ∈ Common.completedDiagonalDomain w) :
    ψ ∈ Common.completedDiagonalDomain (fun n => w n + c) := by
  rw [Common.mem_completedDiagonalDomain_iff]
  let x : (Common.completedDiagonalOperator w).domain := ⟨ψ, hψ⟩
  have hout := lp.memℓp (Common.completedDiagonalOperator w x + c • ψ)
  have hfun :
      (fun n : Occupation Mode => (w n + c) * ψ n) =
        (fun n : Occupation Mode => (Common.completedDiagonalOperator w x + c • ψ) n) := by
    funext n
    change (w n + c) * ψ n = w n * ψ n + c * ψ n
    ring
  rw [hfun]
  exact hout

/-- Removing an occupied mode lowers the free occupation energy by exactly that one-particle
energy. -/
theorem freeHamiltonianWeight_toggle_of_mem (ε : Mode → ℝ)
    {i : Mode} {n : Occupation Mode} (h : i ∈ n) :
    freeHamiltonianWeight ε n =
      freeHamiltonianWeight ε (toggleOccupation i n) + (ε i : ℂ) := by
  rw [toggleOccupation_of_mem h]
  simp only [freeHamiltonianWeight, removeOccupation]
  exact (Finset.sum_erase_add n (fun j => (ε j : ℂ)) h).symm

/-- Adding an unoccupied mode raises the free occupation energy by exactly that one-particle
energy. -/
theorem freeHamiltonianWeight_toggle_of_not_mem (ε : Mode → ℝ)
    {i : Mode} {n : Occupation Mode} (h : i ∉ n) :
    freeHamiltonianWeight ε (toggleOccupation i n) =
      freeHamiltonianWeight ε n + (ε i : ℂ) := by
  rw [toggleOccupation_of_not_mem h]
  simp [freeHamiltonianWeight, insertOccupation, h, add_comm]

/-- Bounded fermionic creation preserves the maximal domain of the completed free Hamiltonian. -/
theorem completedCreate_mem_completedFreeHamiltonianDomain
    (ε : Mode → ℝ) (i : Mode) {ψ : CompletedFockSpace Mode}
    (hψ : ψ ∈ completedFreeHamiltonianDomain ε) :
    completedCreate i ψ ∈ completedFreeHamiltonianDomain ε := by
  change ψ ∈ Common.completedDiagonalDomain (freeHamiltonianWeight ε) at hψ
  change completedCreate i ψ ∈ Common.completedDiagonalDomain (freeHamiltonianWeight ε)
  rw [Common.mem_completedDiagonalDomain_iff]
  have hshift :
      ψ ∈ Common.completedDiagonalDomain
        (fun n => freeHamiltonianWeight ε n + (ε i : ℂ)) :=
    mem_completedDiagonalDomain_add_const (freeHamiltonianWeight ε) (ε i : ℂ) hψ
  let x :
      (Common.completedDiagonalOperator
        (fun n => freeHamiltonianWeight ε n + (ε i : ℂ))).domain := ⟨ψ, hshift⟩
  have hout := lp.memℓp
    (completedToggle i
      (Common.completedDiagonalOperator
        (fun n => freeHamiltonianWeight ε n + (ε i : ℂ)) x))
  exact hout.mono' fun n => by
    by_cases h : i ∈ n
    · rw [completedCreate_apply, if_pos h, completedToggle_apply,
        Common.completedDiagonalOperator_apply, freeHamiltonianWeight_toggle_of_mem ε h]
      simpa [x, norm_fermionPhase]
    · simp only [completedCreate_apply, if_neg h, mul_zero, norm_zero]
      exact norm_nonneg _

/-- Bounded fermionic annihilation preserves the maximal domain of the completed free Hamiltonian. -/
theorem completedAnnihilate_mem_completedFreeHamiltonianDomain
    (ε : Mode → ℝ) (i : Mode) {ψ : CompletedFockSpace Mode}
    (hψ : ψ ∈ completedFreeHamiltonianDomain ε) :
    completedAnnihilate i ψ ∈ completedFreeHamiltonianDomain ε := by
  change ψ ∈ Common.completedDiagonalDomain (freeHamiltonianWeight ε) at hψ
  change completedAnnihilate i ψ ∈ Common.completedDiagonalDomain (freeHamiltonianWeight ε)
  rw [Common.mem_completedDiagonalDomain_iff]
  have hshift :
      ψ ∈ Common.completedDiagonalDomain
        (fun n => freeHamiltonianWeight ε n + (-(ε i : ℂ))) :=
    mem_completedDiagonalDomain_add_const (freeHamiltonianWeight ε) (-(ε i : ℂ)) hψ
  let x :
      (Common.completedDiagonalOperator
        (fun n => freeHamiltonianWeight ε n + (-(ε i : ℂ)))).domain := ⟨ψ, hshift⟩
  have hout := lp.memℓp
    (completedToggle i
      (Common.completedDiagonalOperator
        (fun n => freeHamiltonianWeight ε n + (-(ε i : ℂ))) x))
  exact hout.mono' fun n => by
    by_cases h : i ∈ n
    · simp only [completedAnnihilate_apply, if_pos h, mul_zero, norm_zero]
      exact norm_nonneg _
    · rw [completedAnnihilate_apply, if_neg h, completedToggle_apply,
        Common.completedDiagonalOperator_apply]
      have hE := freeHamiltonianWeight_toggle_of_not_mem ε h
      rw [hE]
      simpa [x, norm_fermionPhase]

/-- Creation restricted to the free-Hamiltonian domain.  This is the domain-preserving map needed
to form `H a†` without pretending that `H` is bounded. -/
noncomputable def completedCreateOnFreeHamiltonianDomain (ε : Mode → ℝ) (i : Mode) :
    completedFreeHamiltonianDomain ε →ₗ[ℂ] completedFreeHamiltonianDomain ε where
  toFun ψ :=
    ⟨completedCreate i (ψ : CompletedFockSpace Mode),
      completedCreate_mem_completedFreeHamiltonianDomain ε i ψ.2⟩
  map_add' ψ φ := by
    apply Subtype.ext
    simp
  map_smul' c ψ := by
    apply Subtype.ext
    simp

/-- Annihilation restricted to the free-Hamiltonian domain. -/
noncomputable def completedAnnihilateOnFreeHamiltonianDomain (ε : Mode → ℝ) (i : Mode) :
    completedFreeHamiltonianDomain ε →ₗ[ℂ] completedFreeHamiltonianDomain ε where
  toFun ψ :=
    ⟨completedAnnihilate i (ψ : CompletedFockSpace Mode),
      completedAnnihilate_mem_completedFreeHamiltonianDomain ε i ψ.2⟩
  map_add' ψ φ := by
    apply Subtype.ext
    simp
  map_smul' c ψ := by
    apply Subtype.ext
    simp

/-- The product `H a†` as an honest linear map on `Dom(H)`. -/
noncomputable def completedFreeHamiltonianAfterCreate (ε : Mode → ℝ) (i : Mode) :
    completedFreeHamiltonianDomain ε →ₗ[ℂ] CompletedFockSpace Mode :=
  (completedFreeHamiltonian ε).toFun.comp (completedCreateOnFreeHamiltonianDomain ε i)

/-- The product `a† H` as an honest linear map on `Dom(H)`. -/
noncomputable def completedCreateAfterFreeHamiltonian (ε : Mode → ℝ) (i : Mode) :
    completedFreeHamiltonianDomain ε →ₗ[ℂ] CompletedFockSpace Mode :=
  (completedCreate i).toLinearMap.comp (completedFreeHamiltonian ε).toFun

/-- The product `H a` as an honest linear map on `Dom(H)`. -/
noncomputable def completedFreeHamiltonianAfterAnnihilate (ε : Mode → ℝ) (i : Mode) :
    completedFreeHamiltonianDomain ε →ₗ[ℂ] CompletedFockSpace Mode :=
  (completedFreeHamiltonian ε).toFun.comp (completedAnnihilateOnFreeHamiltonianDomain ε i)

/-- The product `a H` as an honest linear map on `Dom(H)`. -/
noncomputable def completedAnnihilateAfterFreeHamiltonian (ε : Mode → ℝ) (i : Mode) :
    completedFreeHamiltonianDomain ε →ₗ[ℂ] CompletedFockSpace Mode :=
  (completedAnnihilate i).toLinearMap.comp (completedFreeHamiltonian ε).toFun

end
end Fermionic
end SecondQuantization
