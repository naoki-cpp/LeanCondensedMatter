import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Basic
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.Hamiltonian
import LeanCondensedMatter.QuantumTheory.Gibbs.Eigenbasis
import LeanCondensedMatter.SecondQuantization.Common.Thermal.GrandCanonical
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Core

set_option linter.style.header false

/-!
# Completed free-fermion Gibbs state and ladder intertwining

This module owns the representation-specific completed-Fock-space interface to the generic
pure-point Gibbs state: occupation-basis expectation formulas and the bounded creation/annihilation
intertwining identities used by the completed thermal theory.

The density construction is `Common.grandCanonicalGibbsDensityOperator` on fermionic occupations.
This module supplies only occupation-basis and bounded CAR intertwining results. The Gibbs
generator is `K = H - μ N̂` while physical time evolution remains under `H`.
-/

namespace SecondQuantization
namespace Fermionic

open QuantumTheory

noncomputable section

variable {Mode : Type*}

/-- The generic grand-canonical energy agrees with the fermionic free energy evaluated
at the effective dispersion `ε - μ`. No extra fermion-specific density state is required. -/
private theorem grandCanonicalEnergy_eq_fermionEnergy (ε : Mode → ℝ) (μ : ℝ) :
    Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ =
      fermionEnergy (fun i => ε i - μ) := by
  funext n
  exact Common.grandCanonicalEnergy_eq_shifted ε μ n

/-- Occupation-basis action of the common grand-canonical Gibbs density, in the fermionic
completed-Fock representation. -/
@[simp]
theorem grandCanonicalGibbsDensityOperator_apply_basis
    (ε : Mode → ℝ) (β μ : ℝ)
    (hsum : EigenbasisGibbsSummable
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β)
    (n : Occupation Mode) :
    (Common.grandCanonicalGibbsDensityOperator (Config := Occupation Mode) ε β μ hsum).op
        (completedBasisState n) =
      (eigenbasisGibbsProbability
        (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β n : ℂ) •
        completedBasisState n := by
  simpa only [completedBasisState] using
    (Common.grandCanonicalGibbsDensityOperator_apply_basis
      (Config := Occupation Mode) ε β μ hsum n)

end
end Fermionic
end SecondQuantization

namespace SecondQuantization
namespace Fermionic

open QuantumTheory

noncomputable section

variable {Mode : Type*} [LinearOrder Mode]

private theorem completedFreeGibbsProbability_insertOccupation_of_not_mem
    (ε : Mode → ℝ) (β μ : ℝ) {i : Mode} {n : Occupation Mode} (hi : i ∉ n) :
    eigenbasisGibbsProbability (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β (insertOccupation i n) =
      Real.exp (-β * (ε i - μ)) * eigenbasisGibbsProbability (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β n := by
  simp only [grandCanonicalEnergy_eq_fermionEnergy]
  have hweight :
      eigenbasisBoltzmannWeight (fermionEnergy (fun k => ε k - μ)) β (insertOccupation i n) =
        Real.exp (-β * (ε i - μ)) * eigenbasisBoltzmannWeight (fermionEnergy (fun k => ε k - μ)) β n := by
    change Real.exp (-β * fermionEnergy (fun k => ε k - μ) (insertOccupation i n)) =
      Real.exp (-β * (ε i - μ)) * Real.exp (-β * fermionEnergy (fun k => ε k - μ) n)
    simp only [fermionEnergy_eq_sum, insertOccupation, Finset.sum_insert hi]
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [eigenbasisGibbsProbability, hweight]
  ring

private theorem completedFreeGibbsProbability_removeOccupation_of_mem
    (ε : Mode → ℝ) (β μ : ℝ) {i : Mode} {n : Occupation Mode} (hi : i ∈ n) :
    eigenbasisGibbsProbability (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β (removeOccupation i n) =
      Real.exp (β * (ε i - μ)) * eigenbasisGibbsProbability (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β n := by
  simp only [grandCanonicalEnergy_eq_fermionEnergy]
  have henergy :
      fermionEnergy (fun k => ε k - μ) n = fermionEnergy (fun k => ε k - μ) (removeOccupation i n) + (ε i - μ) := by
    simpa only [fermionEnergy_eq_sum, removeOccupation] using (Finset.sum_erase_add n (fun k => ε k - μ) hi).symm
  have hweight :
      eigenbasisBoltzmannWeight (fermionEnergy (fun k => ε k - μ)) β (removeOccupation i n) =
        Real.exp (β * (ε i - μ)) * eigenbasisBoltzmannWeight (fermionEnergy (fun k => ε k - μ)) β n := by
    change Real.exp (-β * fermionEnergy (fun k => ε k - μ) (removeOccupation i n)) =
      Real.exp (β * (ε i - μ)) * Real.exp (-β * fermionEnergy (fun k => ε k - μ) n)
    rw [henergy, ← Real.exp_add]
    congr 1
    ring
  simp only [eigenbasisGibbsProbability, hweight]
  ring

/-- Complex form of the free Gibbs insertion ratio, matching the scalar used in operator identities. -/
theorem coe_completedFreeGibbsProbability_insertOccupation_of_not_mem
    (ε : Mode → ℝ) (β μ : ℝ) {i : Mode} {n : Occupation Mode} (hi : i ∉ n) :
    (eigenbasisGibbsProbability (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β (insertOccupation i n) : ℂ) =
      Complex.exp (-(β : ℂ) * ((ε i - μ) : ℂ)) *
        (eigenbasisGibbsProbability (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β n : ℂ) := by
  rw [completedFreeGibbsProbability_insertOccupation_of_not_mem ε β μ hi]
  push_cast
  rfl

/-- Complex form of the free Gibbs removal ratio, matching the scalar used in operator identities. -/
theorem coe_completedFreeGibbsProbability_removeOccupation_of_mem
    (ε : Mode → ℝ) (β μ : ℝ) {i : Mode} {n : Occupation Mode} (hi : i ∈ n) :
    (eigenbasisGibbsProbability (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β (removeOccupation i n) : ℂ) =
      Complex.exp ((β : ℂ) * ((ε i - μ) : ℂ)) *
        (eigenbasisGibbsProbability (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β n : ℂ) := by
  rw [completedFreeGibbsProbability_removeOccupation_of_mem ε β μ hi]
  push_cast
  rfl

/-- Completed free-Gibbs creation intertwining:
`ρβ,μ aᵢ† = exp (-β (εᵢ - μ)) aᵢ† ρβ,μ` as an identity of bounded operators. -/
theorem grandCanonicalGibbsDensityOperator_comp_create
    (ε : Mode → ℝ) (β μ : ℝ) (hsum : EigenbasisGibbsSummable
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β) (i : Mode) :
    (Common.grandCanonicalGibbsDensityOperator (Config := Occupation Mode) ε β μ hsum).op.comp (completedCreate i) =
      Complex.exp (-(β : ℂ) * ((ε i - μ : ℝ) : ℂ)) •
        ((completedCreate i).comp
          (Common.grandCanonicalGibbsDensityOperator (Config := Occupation Mode) ε β μ hsum).op) := by
  apply Common.continuousLinearMap_ext_completedBasis
  intro n
  change
    (Common.grandCanonicalGibbsDensityOperator (Config := Occupation Mode) ε β μ hsum).op
        (completedCreate i (completedBasisState n)) =
      Complex.exp (-(β : ℂ) * ((ε i - μ : ℝ) : ℂ)) •
        completedCreate i
          ((Common.grandCanonicalGibbsDensityOperator (Config := Occupation Mode) ε β μ hsum).op (completedBasisState n))
  by_cases hi : i ∈ n
  · rw [completedCreate_basisState_of_mem hi, map_zero,
      grandCanonicalGibbsDensityOperator_apply_basis, map_smul,
      completedCreate_basisState_of_mem hi]
    simp
  · rw [completedCreate_basisState_of_not_mem hi, map_smul,
      grandCanonicalGibbsDensityOperator_apply_basis,
      grandCanonicalGibbsDensityOperator_apply_basis, map_smul,
      completedCreate_basisState_of_not_mem hi,
      coe_completedFreeGibbsProbability_insertOccupation_of_not_mem ε β μ hi]
    have hcast : ((ε i - μ : ℝ) : ℂ) = (ε i : ℂ) - (μ : ℂ) := by
      push_cast
      ring
    rw [hcast]
    simp only [smul_smul]
    congr 1
    ring

/-- Completed free-Gibbs annihilation intertwining:
`ρβ,μ aᵢ = exp (β (εᵢ - μ)) aᵢ ρβ,μ` as an identity of bounded operators. -/
theorem grandCanonicalGibbsDensityOperator_comp_annihilate
    (ε : Mode → ℝ) (β μ : ℝ) (hsum : EigenbasisGibbsSummable
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β) (i : Mode) :
    (Common.grandCanonicalGibbsDensityOperator (Config := Occupation Mode) ε β μ hsum).op.comp (completedAnnihilate i) =
      Complex.exp ((β : ℂ) * ((ε i - μ : ℝ) : ℂ)) •
        ((completedAnnihilate i).comp
          (Common.grandCanonicalGibbsDensityOperator (Config := Occupation Mode) ε β μ hsum).op) := by
  apply Common.continuousLinearMap_ext_completedBasis
  intro n
  change
    (Common.grandCanonicalGibbsDensityOperator (Config := Occupation Mode) ε β μ hsum).op
        (completedAnnihilate i (completedBasisState n)) =
      Complex.exp ((β : ℂ) * ((ε i - μ : ℝ) : ℂ)) •
        completedAnnihilate i
          ((Common.grandCanonicalGibbsDensityOperator (Config := Occupation Mode) ε β μ hsum).op (completedBasisState n))
  by_cases hi : i ∈ n
  · rw [completedAnnihilate_basisState_of_mem hi, map_smul,
      grandCanonicalGibbsDensityOperator_apply_basis,
      grandCanonicalGibbsDensityOperator_apply_basis, map_smul,
      completedAnnihilate_basisState_of_mem hi,
      coe_completedFreeGibbsProbability_removeOccupation_of_mem ε β μ hi]
    have hcast : ((ε i - μ : ℝ) : ℂ) = (ε i : ℂ) - (μ : ℂ) := by
      push_cast
      ring
    rw [hcast]
    simp only [smul_smul]
    congr 1
    ring
  · rw [completedAnnihilate_basisState_of_not_mem hi, map_zero,
      grandCanonicalGibbsDensityOperator_apply_basis, map_smul,
      completedAnnihilate_basisState_of_not_mem hi]
    simp

end
end Fermionic
end SecondQuantization
