import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Basic
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.Hamiltonian
import LeanCondensedMatter.QuantumTheory.Gibbs.Eigenbasis
import LeanCondensedMatter.SecondQuantization.Common.Thermal.GrandCanonical
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Core

set_option linter.style.header false

/-!
# Completed free-fermion Gibbs state and ladder intertwining

The common pure-point grand-canonical Gibbs density acts on fermionic occupations.
This module proves its bounded creation/annihilation intertwining identities directly
from the common occupation-basis action and the fermionic occupation-shift formulas.
The Gibbs generator is `K = H - μ N̂` while physical time evolution remains under `H`.
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
  have hρ (m : Occupation Mode) :
      (Common.grandCanonicalGibbsDensityOperator (Config := Occupation Mode) ε β μ hsum).op
          (completedBasisState m) =
        (eigenbasisGibbsProbability
          (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β m : ℂ) •
          completedBasisState m := by
    simpa only [completedBasisState] using
      (Common.grandCanonicalGibbsDensityOperator_apply_basis
        (Config := Occupation Mode) ε β μ hsum m)
  by_cases hi : i ∈ n
  · rw [completedCreate_basisState_of_mem hi, map_zero,
      hρ, map_smul,
      completedCreate_basisState_of_mem hi]
    simp
  · have hprob :
        (eigenbasisGibbsProbability
          (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β
          (insertOccupation i n) : ℂ) =
        Complex.exp (-(β : ℂ) * ((ε i - μ) : ℂ)) *
          (eigenbasisGibbsProbability
            (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β n : ℂ) := by
      rw [completedFreeGibbsProbability_insertOccupation_of_not_mem ε β μ hi]
      push_cast
      rfl
    rw [completedCreate_basisState_of_not_mem hi, map_smul,
      hρ,
      hρ, map_smul,
      completedCreate_basisState_of_not_mem hi, hprob]
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
  have hρ (m : Occupation Mode) :
      (Common.grandCanonicalGibbsDensityOperator (Config := Occupation Mode) ε β μ hsum).op
          (completedBasisState m) =
        (eigenbasisGibbsProbability
          (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β m : ℂ) •
          completedBasisState m := by
    simpa only [completedBasisState] using
      (Common.grandCanonicalGibbsDensityOperator_apply_basis
        (Config := Occupation Mode) ε β μ hsum m)
  by_cases hi : i ∈ n
  · have hprob :
        (eigenbasisGibbsProbability
          (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β
          (removeOccupation i n) : ℂ) =
        Complex.exp ((β : ℂ) * ((ε i - μ) : ℂ)) *
          (eigenbasisGibbsProbability
            (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β n : ℂ) := by
      rw [completedFreeGibbsProbability_removeOccupation_of_mem ε β μ hi]
      push_cast
      rfl
    rw [completedAnnihilate_basisState_of_mem hi, map_smul,
      hρ,
      hρ, map_smul,
      completedAnnihilate_basisState_of_mem hi, hprob]
    have hcast : ((ε i - μ : ℝ) : ℂ) = (ε i : ℂ) - (μ : ℂ) := by
      push_cast
      ring
    rw [hcast]
    simp only [smul_smul]
    congr 1
    ring
  · rw [completedAnnihilate_basisState_of_not_mem hi, map_zero,
      hρ, map_smul,
      completedAnnihilate_basisState_of_not_mem hi]
    simp

end
end Fermionic
end SecondQuantization
