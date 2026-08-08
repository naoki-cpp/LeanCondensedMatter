import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.ProductDomain

set_option linter.style.header false

/-!
# Free-Hamiltonian ladder relations on the completed fermionic domain

The bounded fermionic ladder operators preserve the maximal domain of the completed free
Hamiltonian.  This file uses that domain invariance to state the usual free-energy commutator
relations as honest identities of linear maps on `Dom(H)`:

`[H, aᵢ†] = εᵢ aᵢ†` and `[H, aᵢ] = -εᵢ aᵢ`.

No product of unbounded operators is formed on the ambient completed Fock space.  Both sides are
maps whose source is the explicit free-Hamiltonian domain supplied by `ProductDomain.lean`.
-/

namespace SecondQuantization
namespace Fermionic

noncomputable section

variable {Mode : Type*} [LinearOrder Mode]

/-- Creation viewed as an ambient-valued linear map whose source is `Dom(H)`. -/
noncomputable def completedCreateFromFreeHamiltonianDomain (ε : Mode → ℝ) (i : Mode) :
    completedFreeHamiltonianDomain ε →ₗ[ℂ] CompletedFockSpace Mode :=
  (completedCreate i).toLinearMap.comp (completedFreeHamiltonianDomain ε).subtype

/-- Annihilation viewed as an ambient-valued linear map whose source is `Dom(H)`. -/
noncomputable def completedAnnihilateFromFreeHamiltonianDomain (ε : Mode → ℝ) (i : Mode) :
    completedFreeHamiltonianDomain ε →ₗ[ℂ] CompletedFockSpace Mode :=
  (completedAnnihilate i).toLinearMap.comp (completedFreeHamiltonianDomain ε).subtype

/-- Pointwise free-Hamiltonian commutator relation for fermionic creation on `Dom(H)`. -/
theorem completedFreeHamiltonian_create_commutator_apply
    (ε : Mode → ℝ) (i : Mode) (ψ : completedFreeHamiltonianDomain ε) :
    completedFreeHamiltonianAfterCreate ε i ψ -
        completedCreateAfterFreeHamiltonian ε i ψ =
      (ε i : ℂ) • completedCreateFromFreeHamiltonianDomain ε i ψ := by
  apply lp.ext
  funext n
  have hHa :
      completedFreeHamiltonianAfterCreate ε i ψ n =
        freeHamiltonianWeight ε n *
          completedCreate i (ψ : CompletedFockSpace Mode) n := by
    rfl
  have haH :
      completedCreateAfterFreeHamiltonian ε i ψ n =
        completedCreate i ((completedFreeHamiltonian ε).toFun ψ) n := by
    rfl
  have hH (m : Occupation Mode) :
      (completedFreeHamiltonian ε).toFun ψ m =
        freeHamiltonianWeight ε m * (ψ : CompletedFockSpace Mode) m := by
    rfl
  rw [hHa, haH]
  change
    freeHamiltonianWeight ε n * completedCreate i (ψ : CompletedFockSpace Mode) n -
        completedCreate i ((completedFreeHamiltonian ε).toFun ψ) n =
      (ε i : ℂ) * completedCreate i (ψ : CompletedFockSpace Mode) n
  rw [completedCreate_apply, completedCreate_apply]
  by_cases h : i ∈ n
  · simp only [if_pos h]
    rw [hH, freeHamiltonianWeight_toggle_of_mem ε h]
    ring
  · simp [h]

/-- The completed free-Hamiltonian creation commutator as an identity of linear maps on `Dom(H)`. -/
theorem completedFreeHamiltonian_create_commutator (ε : Mode → ℝ) (i : Mode) :
    completedFreeHamiltonianAfterCreate ε i - completedCreateAfterFreeHamiltonian ε i =
      (ε i : ℂ) • completedCreateFromFreeHamiltonianDomain ε i := by
  ext ψ
  exact completedFreeHamiltonian_create_commutator_apply ε i ψ

/-- Pointwise free-Hamiltonian commutator relation for fermionic annihilation on `Dom(H)`. -/
theorem completedFreeHamiltonian_annihilate_commutator_apply
    (ε : Mode → ℝ) (i : Mode) (ψ : completedFreeHamiltonianDomain ε) :
    completedFreeHamiltonianAfterAnnihilate ε i ψ -
        completedAnnihilateAfterFreeHamiltonian ε i ψ =
      (-(ε i : ℂ)) • completedAnnihilateFromFreeHamiltonianDomain ε i ψ := by
  apply lp.ext
  funext n
  have hHa :
      completedFreeHamiltonianAfterAnnihilate ε i ψ n =
        freeHamiltonianWeight ε n *
          completedAnnihilate i (ψ : CompletedFockSpace Mode) n := by
    rfl
  have haH :
      completedAnnihilateAfterFreeHamiltonian ε i ψ n =
        completedAnnihilate i ((completedFreeHamiltonian ε).toFun ψ) n := by
    rfl
  have hH (m : Occupation Mode) :
      (completedFreeHamiltonian ε).toFun ψ m =
        freeHamiltonianWeight ε m * (ψ : CompletedFockSpace Mode) m := by
    rfl
  rw [hHa, haH]
  change
    freeHamiltonianWeight ε n * completedAnnihilate i (ψ : CompletedFockSpace Mode) n -
        completedAnnihilate i ((completedFreeHamiltonian ε).toFun ψ) n =
      (-(ε i : ℂ)) * completedAnnihilate i (ψ : CompletedFockSpace Mode) n
  rw [completedAnnihilate_apply, completedAnnihilate_apply]
  by_cases h : i ∈ n
  · simp [h]
  · simp only [if_neg h]
    rw [hH, freeHamiltonianWeight_toggle_of_not_mem ε h]
    ring

/-- The completed free-Hamiltonian annihilation commutator as an identity of linear maps on
`Dom(H)`. -/
theorem completedFreeHamiltonian_annihilate_commutator (ε : Mode → ℝ) (i : Mode) :
    completedFreeHamiltonianAfterAnnihilate ε i - completedAnnihilateAfterFreeHamiltonian ε i =
      (-(ε i : ℂ)) • completedAnnihilateFromFreeHamiltonianDomain ε i := by
  ext ψ
  exact completedFreeHamiltonian_annihilate_commutator_apply ε i ψ

end
end Fermionic
end SecondQuantization
