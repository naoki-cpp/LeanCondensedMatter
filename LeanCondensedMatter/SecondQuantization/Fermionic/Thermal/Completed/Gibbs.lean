import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Basic
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.Hamiltonian
import LeanCondensedMatter.QuantumTheory.Gibbs.Eigenbasis
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Core

set_option linter.style.header false

/-!
# Completed free-fermion Gibbs state and ladder intertwining

This module owns the representation-specific completed-Fock-space interface to the generic
pure-point Gibbs state: occupation-basis expectation formulas and the bounded creation/annihilation
intertwining identities used by the completed thermal theory.

Boltzmann weights, partition functions, normalized probabilities, and the density-state construction
remain owned by `QuantumTheory.Gibbs.Eigenbasis`.
-/

namespace SecondQuantization
namespace Fermionic

open QuantumTheory

noncomputable section

variable {Mode : Type*}

/-- The canonical free-fermion Gibbs density operator on the completed occupation Fock space. -/
noncomputable def completedFreeGibbsDensityOperator
    (ε : Mode → ℝ) (β : ℝ) (hsum : EigenbasisGibbsSummable (fermionEnergy ε) β) :
    DensityOperator (CompletedFockSpace Mode) :=
  eigenbasisGibbsDensityOperator completedOccupationHilbertBasis (fermionEnergy ε) β hsum

/-- The completed free Gibbs density operator acts diagonally in the occupation basis. -/
@[simp]
theorem completedFreeGibbsDensityOperator_apply_basis
    (ε : Mode → ℝ) (β : ℝ) (hsum : EigenbasisGibbsSummable (fermionEnergy ε) β)
    (n : Occupation Mode) :
    (completedFreeGibbsDensityOperator ε β hsum).op (completedBasisState n) =
      (eigenbasisGibbsProbability (fermionEnergy ε) β n : ℂ) • completedBasisState n := by
  simpa [completedFreeGibbsDensityOperator] using
    eigenbasisGibbsDensityOperator_apply_basis
      (completedOccupationHilbertBasis (Mode := Mode)) (fermionEnergy ε) β hsum n

end
end Fermionic
end SecondQuantization

namespace SecondQuantization
namespace Fermionic

open QuantumTheory

noncomputable section

variable {Mode : Type*} [LinearOrder Mode]

private theorem completedFreeGibbsProbability_insertOccupation_of_not_mem
    (ε : Mode → ℝ) (β : ℝ) {i : Mode} {n : Occupation Mode} (hi : i ∉ n) :
    eigenbasisGibbsProbability (fermionEnergy ε) β (insertOccupation i n) =
      Real.exp (-β * ε i) * eigenbasisGibbsProbability (fermionEnergy ε) β n := by
  have hweight :
      eigenbasisBoltzmannWeight (fermionEnergy ε) β (insertOccupation i n) =
        Real.exp (-β * ε i) * eigenbasisBoltzmannWeight (fermionEnergy ε) β n := by
    change Real.exp (-β * fermionEnergy ε (insertOccupation i n)) =
      Real.exp (-β * ε i) * Real.exp (-β * fermionEnergy ε n)
    simp only [fermionEnergy, insertOccupation, Finset.sum_insert hi]
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [eigenbasisGibbsProbability, hweight]
  ring

private theorem completedFreeGibbsProbability_removeOccupation_of_mem
    (ε : Mode → ℝ) (β : ℝ) {i : Mode} {n : Occupation Mode} (hi : i ∈ n) :
    eigenbasisGibbsProbability (fermionEnergy ε) β (removeOccupation i n) =
      Real.exp (β * ε i) * eigenbasisGibbsProbability (fermionEnergy ε) β n := by
  have henergy :
      fermionEnergy ε n = fermionEnergy ε (removeOccupation i n) + ε i := by
    simpa [fermionEnergy, removeOccupation] using (Finset.sum_erase_add n ε hi).symm
  have hweight :
      eigenbasisBoltzmannWeight (fermionEnergy ε) β (removeOccupation i n) =
        Real.exp (β * ε i) * eigenbasisBoltzmannWeight (fermionEnergy ε) β n := by
    change Real.exp (-β * fermionEnergy ε (removeOccupation i n)) =
      Real.exp (β * ε i) * Real.exp (-β * fermionEnergy ε n)
    rw [henergy, ← Real.exp_add]
    congr 1
    ring
  simp only [eigenbasisGibbsProbability, hweight]
  ring

/-- Complex form of the free Gibbs insertion ratio, matching the scalar used in operator identities. -/
theorem coe_completedFreeGibbsProbability_insertOccupation_of_not_mem
    (ε : Mode → ℝ) (β : ℝ) {i : Mode} {n : Occupation Mode} (hi : i ∉ n) :
    (eigenbasisGibbsProbability (fermionEnergy ε) β (insertOccupation i n) : ℂ) =
      Complex.exp (-(β : ℂ) * (ε i : ℂ)) *
        (eigenbasisGibbsProbability (fermionEnergy ε) β n : ℂ) := by
  rw [completedFreeGibbsProbability_insertOccupation_of_not_mem ε β hi]
  push_cast
  rfl

/-- Complex form of the free Gibbs removal ratio, matching the scalar used in operator identities. -/
theorem coe_completedFreeGibbsProbability_removeOccupation_of_mem
    (ε : Mode → ℝ) (β : ℝ) {i : Mode} {n : Occupation Mode} (hi : i ∈ n) :
    (eigenbasisGibbsProbability (fermionEnergy ε) β (removeOccupation i n) : ℂ) =
      Complex.exp ((β : ℂ) * (ε i : ℂ)) *
        (eigenbasisGibbsProbability (fermionEnergy ε) β n : ℂ) := by
  rw [completedFreeGibbsProbability_removeOccupation_of_mem ε β hi]
  push_cast
  rfl

/-- Completed free-Gibbs creation intertwining:
`ρβ aᵢ† = exp (-β εᵢ) aᵢ† ρβ` as an identity of bounded operators. -/
theorem completedFreeGibbsDensityOperator_comp_create
    (ε : Mode → ℝ) (β : ℝ) (hsum : EigenbasisGibbsSummable (fermionEnergy ε) β) (i : Mode) :
    (completedFreeGibbsDensityOperator ε β hsum).op.comp (completedCreate i) =
      Complex.exp (-(β : ℂ) * (ε i : ℂ)) •
        ((completedCreate i).comp
          (completedFreeGibbsDensityOperator ε β hsum).op) := by
  apply Common.continuousLinearMap_ext_completedBasis
  intro n
  change
    (completedFreeGibbsDensityOperator ε β hsum).op
        (completedCreate i (completedBasisState n)) =
      Complex.exp (-(β : ℂ) * (ε i : ℂ)) •
        completedCreate i
          ((completedFreeGibbsDensityOperator ε β hsum).op (completedBasisState n))
  by_cases hi : i ∈ n
  · rw [completedCreate_basisState_of_mem hi, map_zero,
      completedFreeGibbsDensityOperator_apply_basis, map_smul,
      completedCreate_basisState_of_mem hi]
    simp
  · rw [completedCreate_basisState_of_not_mem hi, map_smul,
      completedFreeGibbsDensityOperator_apply_basis,
      completedFreeGibbsDensityOperator_apply_basis, map_smul,
      completedCreate_basisState_of_not_mem hi,
      coe_completedFreeGibbsProbability_insertOccupation_of_not_mem ε β hi]
    simp only [smul_smul]
    congr 1
    ring

/-- Completed free-Gibbs annihilation intertwining:
`ρβ aᵢ = exp (β εᵢ) aᵢ ρβ` as an identity of bounded operators. -/
theorem completedFreeGibbsDensityOperator_comp_annihilate
    (ε : Mode → ℝ) (β : ℝ) (hsum : EigenbasisGibbsSummable (fermionEnergy ε) β) (i : Mode) :
    (completedFreeGibbsDensityOperator ε β hsum).op.comp (completedAnnihilate i) =
      Complex.exp ((β : ℂ) * (ε i : ℂ)) •
        ((completedAnnihilate i).comp
          (completedFreeGibbsDensityOperator ε β hsum).op) := by
  apply Common.continuousLinearMap_ext_completedBasis
  intro n
  change
    (completedFreeGibbsDensityOperator ε β hsum).op
        (completedAnnihilate i (completedBasisState n)) =
      Complex.exp ((β : ℂ) * (ε i : ℂ)) •
        completedAnnihilate i
          ((completedFreeGibbsDensityOperator ε β hsum).op (completedBasisState n))
  by_cases hi : i ∈ n
  · rw [completedAnnihilate_basisState_of_mem hi, map_smul,
      completedFreeGibbsDensityOperator_apply_basis,
      completedFreeGibbsDensityOperator_apply_basis, map_smul,
      completedAnnihilate_basisState_of_mem hi,
      coe_completedFreeGibbsProbability_removeOccupation_of_mem ε β hi]
    simp only [smul_smul]
    congr 1
    ring
  · rw [completedAnnihilate_basisState_of_not_mem hi, map_zero,
      completedFreeGibbsDensityOperator_apply_basis, map_smul,
      completedAnnihilate_basisState_of_not_mem hi]
    simp

end
end Fermionic
end SecondQuantization
