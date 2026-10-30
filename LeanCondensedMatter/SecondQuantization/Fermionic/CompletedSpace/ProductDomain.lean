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
scalar `ε i`.  The generic stability of weighted diagonal domains under a finite scalar shift is
owned by `Common.CompletedSpace.Diagonal`; this file combines it with the occupation toggle to prove
domain invariance of the free Hamiltonian under both bounded ladder operators.
-/

namespace SecondQuantization
namespace Fermionic

open scoped ENNReal

noncomputable section

variable {Mode : Type*} [LinearOrder Mode]

/-- Removing an occupied mode lowers the free occupation energy by exactly that one-particle
energy. -/
theorem freeHamiltonianWeight_toggle_of_mem (ε : Mode → ℝ)
    {i : Mode} {n : Occupation Mode} (h : i ∈ n) :
    freeHamiltonianWeight ε n =
      freeHamiltonianWeight ε (toggleOccupation i n) + (ε i : ℂ) := by
  rw [toggleOccupation_of_mem h]
  have hE : fermionEnergy ε n = fermionEnergy ε (removeOccupation i n) + ε i :=
    (sub_eq_iff_eq_add.mp (fermionEnergy_removeOccupation_of_mem (ε := ε) h).symm)
  simpa [freeHamiltonianWeight] using congrArg (fun x : ℝ => (x : ℂ)) hE

/-- Adding an unoccupied mode raises the free occupation energy by exactly that one-particle
energy. -/
theorem freeHamiltonianWeight_toggle_of_not_mem (ε : Mode → ℝ)
    {i : Mode} {n : Occupation Mode} (h : i ∉ n) :
    freeHamiltonianWeight ε (toggleOccupation i n) =
      freeHamiltonianWeight ε n + (ε i : ℂ) := by
  rw [toggleOccupation_of_not_mem h]
  simpa [freeHamiltonianWeight] using
    congrArg (fun x : ℝ => (x : ℂ)) (fermionEnergy_insertOccupation_of_not_mem (ε := ε) h)

/-! A weighted toggle bound transfers maximal diagonal-domain membership.
The finite constant shift is handled by the Common diagonal-domain theorem. -/
private theorem mem_completedFreeHamiltonianDomain_of_toggle_bound
    (ε : Mode → ℝ) (i : Mode) (c : ℂ)
    {ψ φ : CompletedFockSpace Mode}
    (hψ : ψ ∈ completedFreeHamiltonianDomain ε)
    (hbound : ∀ n : Occupation Mode,
      ‖freeHamiltonianWeight ε n * φ n‖ ≤
        ‖(freeHamiltonianWeight ε (toggleOccupation i n) + c) *
          ψ (toggleOccupation i n)‖) :
    φ ∈ completedFreeHamiltonianDomain ε := by
  change ψ ∈ Common.completedDiagonalDomain (freeHamiltonianWeight ε) at hψ
  change φ ∈ Common.completedDiagonalDomain (freeHamiltonianWeight ε)
  rw [Common.mem_completedDiagonalDomain_iff]
  have hshift :
      ψ ∈ Common.completedDiagonalDomain
        (fun n => freeHamiltonianWeight ε n + c) :=
    Common.mem_completedDiagonalDomain_add_const (freeHamiltonianWeight ε) c hψ
  let x :
      (Common.completedDiagonalOperator
        (fun n => freeHamiltonianWeight ε n + c)).domain := ⟨ψ, hshift⟩
  have hout := lp.memℓp
    (Common.completedReindex (toggleOccupationEquiv i)
      (Common.completedDiagonalOperator
        (fun n => freeHamiltonianWeight ε n + c) x))
  exact hout.mono' fun n => by
    rw [Common.completedReindex_apply, toggleOccupationEquiv_apply,
      Common.completedDiagonalOperator_apply]
    exact hbound n

/-- Bounded fermionic creation preserves the maximal domain of the completed free Hamiltonian. -/
theorem completedCreate_mem_completedFreeHamiltonianDomain
    (ε : Mode → ℝ) (i : Mode) {ψ : CompletedFockSpace Mode}
    (hψ : ψ ∈ completedFreeHamiltonianDomain ε) :
    completedCreate i ψ ∈ completedFreeHamiltonianDomain ε := by
  apply mem_completedFreeHamiltonianDomain_of_toggle_bound ε i (ε i : ℂ) hψ
  intro n
  by_cases h : i ∈ n
  · rw [completedCreate_apply, ite_eq_left h,
      freeHamiltonianWeight_toggle_of_mem ε h]
    simp [norm_fermionPhase]
  · rw [completedCreate_apply, ite_eq_right h]
    simp only [zero_mul, norm_zero, norm_mul]
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)

/-- Bounded fermionic annihilation preserves the maximal domain of the completed free Hamiltonian. -/
theorem completedAnnihilate_mem_completedFreeHamiltonianDomain
    (ε : Mode → ℝ) (i : Mode) {ψ : CompletedFockSpace Mode}
    (hψ : ψ ∈ completedFreeHamiltonianDomain ε) :
    completedAnnihilate i ψ ∈ completedFreeHamiltonianDomain ε := by
  apply mem_completedFreeHamiltonianDomain_of_toggle_bound ε i (-(ε i : ℂ)) hψ
  intro n
  by_cases h : i ∈ n
  · rw [completedAnnihilate_apply, ite_eq_left h]
    simp only [zero_mul, norm_zero, norm_mul]
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  · rw [completedAnnihilate_apply, ite_eq_right h]
    rw [freeHamiltonianWeight_toggle_of_not_mem ε h]
    simpa [norm_mul, norm_fermionPhase]

/-- The product `H a†` as an honest linear map on `Dom(H)`. -/
noncomputable def completedFreeHamiltonianAfterCreate (ε : Mode → ℝ) (i : Mode) :
    completedFreeHamiltonianDomain ε →ₗ[ℂ] CompletedFockSpace Mode :=
  (completedFreeHamiltonian ε).toFun.comp <|
    (completedCreate i).toLinearMap.restrict
      (p := completedFreeHamiltonianDomain ε) (q := completedFreeHamiltonianDomain ε)
      (fun _ hψ => completedCreate_mem_completedFreeHamiltonianDomain ε i hψ)

/-- The product `a† H` as an honest linear map on `Dom(H)`. -/
noncomputable def completedCreateAfterFreeHamiltonian (ε : Mode → ℝ) (i : Mode) :
    completedFreeHamiltonianDomain ε →ₗ[ℂ] CompletedFockSpace Mode :=
  (completedCreate i).toLinearMap.comp (completedFreeHamiltonian ε).toFun

/-- The product `H a` as an honest linear map on `Dom(H)`. -/
noncomputable def completedFreeHamiltonianAfterAnnihilate (ε : Mode → ℝ) (i : Mode) :
    completedFreeHamiltonianDomain ε →ₗ[ℂ] CompletedFockSpace Mode :=
  (completedFreeHamiltonian ε).toFun.comp <|
    (completedAnnihilate i).toLinearMap.restrict
      (p := completedFreeHamiltonianDomain ε) (q := completedFreeHamiltonianDomain ε)
      (fun _ hψ => completedAnnihilate_mem_completedFreeHamiltonianDomain ε i hψ)

/-- The product `a H` as an honest linear map on `Dom(H)`. -/
noncomputable def completedAnnihilateAfterFreeHamiltonian (ε : Mode → ℝ) (i : Mode) :
    completedFreeHamiltonianDomain ε →ₗ[ℂ] CompletedFockSpace Mode :=
  (completedAnnihilate i).toLinearMap.comp (completedFreeHamiltonian ε).toFun

end
end Fermionic
end SecondQuantization
