import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.Hamiltonian
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Core
import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.Diagonal
import LeanCondensedMatter.QuantumTheory.Gibbs.PurePoint

set_option linter.style.header false

/-!
# Bounded free-fermion heat operator on completed Fock space

The unnormalized heat operator only needs uniform boundedness of the Boltzmann weights, not
trace-classness or finiteness of the partition function. This file isolates that weaker completed-
space layer from the normalized Gibbs density state.

A lower bound on the many-body free energy at nonnegative inverse temperature is a sufficient
condition for boundedness. Gibbs summability is another, strictly stronger, sufficient condition.
-/

namespace SecondQuantization
namespace Fermionic

open QuantumTheory

noncomputable section

variable {Mode : Type*}

/-- The free Boltzmann weights are uniformly bounded on the completed occupation basis. This is the
minimal diagonal-multiplier condition used to construct the bounded heat operator; it does not
assert trace-classness or summability of the weights. -/
def CompletedFreeHeatBounded (ε : Mode → ℝ) (β : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n : Occupation Mode,
    ‖(purePointBoltzmannWeight (fermionEnergy ε) β n : ℂ)‖ ≤ C

/-- A lower bound on the many-body free energy makes the heat weights uniformly bounded at
nonnegative inverse temperature. -/
theorem completedFreeHeatBounded_of_lowerBound
    (ε : Mode → ℝ) (β L : ℝ) (hβ : 0 ≤ β)
    (hE : ∀ n : Occupation Mode, L ≤ fermionEnergy ε n) :
    CompletedFreeHeatBounded ε β := by
  refine ⟨Real.exp (-β * L), (Real.exp_pos _).le, ?_⟩
  intro n
  change ‖((Real.exp (-β * fermionEnergy ε n) : ℝ) : ℂ)‖ ≤ Real.exp (-β * L)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_left (hE n) hβ
  simpa [neg_mul] using neg_le_neg hmul

/-- Gibbs summability implies boundedness of the heat weights. This is the bridge from the existing
trace-class/Gibbs-state layer to the weaker bounded heat-operator layer. -/
theorem completedFreeHeatBounded_of_gibbsSummable
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β) :
    CompletedFreeHeatBounded ε β := by
  change Summable (fun n : Occupation Mode =>
    ‖purePointBoltzmannWeight (fermionEnergy ε) β n‖) at hsum
  refine ⟨∑' n : Occupation Mode, ‖purePointBoltzmannWeight (fermionEnergy ε) β n‖,
    tsum_nonneg fun _ => norm_nonneg _, ?_⟩
  intro n
  have hle := hsum.le_tsum n
    (fun m _ => norm_nonneg (purePointBoltzmannWeight (fermionEnergy ε) β m))
  simpa [Complex.norm_real, Real.norm_eq_abs] using hle

/-- The bounded unnormalized free heat operator on completed fermionic Fock space. -/
noncomputable def completedFreeHeatOperator
    (ε : Mode → ℝ) (β : ℝ) (hbounded : CompletedFreeHeatBounded ε β) :
    CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode :=
  Common.completedBoundedDiagonalOperator
    (fun n : Occupation Mode => (purePointBoltzmannWeight (fermionEnergy ε) β n : ℂ))
    (Classical.choose_spec hbounded).1
    (Classical.choose_spec hbounded).2

/-- The completed free heat operator acts by the Boltzmann weight on each occupation basis state. -/
@[simp]
theorem completedFreeHeatOperator_apply_basis
    (ε : Mode → ℝ) (β : ℝ) (hbounded : CompletedFreeHeatBounded ε β)
    (n : Occupation Mode) :
    completedFreeHeatOperator ε β hbounded (completedBasisState n) =
      (purePointBoltzmannWeight (fermionEnergy ε) β n : ℂ) • completedBasisState n := by
  simpa [completedFreeHeatOperator] using
    Common.completedBoundedDiagonalOperator_basisState
      (fun m : Occupation Mode =>
        (purePointBoltzmannWeight (fermionEnergy ε) β m : ℂ))
      (Classical.choose_spec hbounded).1
      (Classical.choose_spec hbounded).2 n

end
end Fermionic
end SecondQuantization

namespace SecondQuantization
namespace Fermionic

open QuantumTheory

noncomputable section

variable {Mode : Type*} [LinearOrder Mode]

private theorem coe_completedFreeBoltzmannWeight_insertOccupation_of_not_mem
    (ε : Mode → ℝ) (β : ℝ) {i : Mode} {n : Occupation Mode} (hi : i ∉ n) :
    (purePointBoltzmannWeight (fermionEnergy ε) β (insertOccupation i n) : ℂ) =
      Complex.exp (-(β : ℂ) * (ε i : ℂ)) *
        (purePointBoltzmannWeight (fermionEnergy ε) β n : ℂ) := by
  have hweight :
      purePointBoltzmannWeight (fermionEnergy ε) β (insertOccupation i n) =
        Real.exp (-β * ε i) * purePointBoltzmannWeight (fermionEnergy ε) β n := by
    change Real.exp (-β * fermionEnergy ε (insertOccupation i n)) =
      Real.exp (-β * ε i) * Real.exp (-β * fermionEnergy ε n)
    rw [fermionEnergy_insertOccupation_of_not_mem hi, ← Real.exp_add]
    congr 1
    ring
  rw [hweight]
  push_cast
  rfl

private theorem coe_completedFreeBoltzmannWeight_removeOccupation_of_mem
    (ε : Mode → ℝ) (β : ℝ) {i : Mode} {n : Occupation Mode} (hi : i ∈ n) :
    (purePointBoltzmannWeight (fermionEnergy ε) β (removeOccupation i n) : ℂ) =
      Complex.exp ((β : ℂ) * (ε i : ℂ)) *
        (purePointBoltzmannWeight (fermionEnergy ε) β n : ℂ) := by
  have hweight :
      purePointBoltzmannWeight (fermionEnergy ε) β (removeOccupation i n) =
        Real.exp (β * ε i) * purePointBoltzmannWeight (fermionEnergy ε) β n := by
    change Real.exp (-β * fermionEnergy ε (removeOccupation i n)) =
      Real.exp (β * ε i) * Real.exp (-β * fermionEnergy ε n)
    rw [fermionEnergy_removeOccupation_of_mem hi, ← Real.exp_add]
    congr 1
    ring
  rw [hweight]
  push_cast
  rfl

/-- Trace-class-free creation intertwining for the bounded free heat operator:
`Kβ aᵢ† = exp (-β εᵢ) aᵢ† Kβ`. -/
theorem completedFreeHeatOperator_comp_create
    (ε : Mode → ℝ) (β : ℝ) (hbounded : CompletedFreeHeatBounded ε β) (i : Mode) :
    (completedFreeHeatOperator ε β hbounded).comp (completedCreate i) =
      Complex.exp (-(β : ℂ) * (ε i : ℂ)) •
        ((completedCreate i).comp (completedFreeHeatOperator ε β hbounded)) := by
  apply Common.continuousLinearMap_ext_completedBasis
  intro n
  change
    completedFreeHeatOperator ε β hbounded
        (completedCreate i (completedBasisState n)) =
      Complex.exp (-(β : ℂ) * (ε i : ℂ)) •
        completedCreate i
          (completedFreeHeatOperator ε β hbounded (completedBasisState n))
  by_cases hi : i ∈ n
  · rw [completedCreate_basisState_of_mem hi, map_zero,
      completedFreeHeatOperator_apply_basis, map_smul,
      completedCreate_basisState_of_mem hi]
    simp
  · rw [completedCreate_basisState_of_not_mem hi, map_smul,
      completedFreeHeatOperator_apply_basis,
      completedFreeHeatOperator_apply_basis, map_smul,
      completedCreate_basisState_of_not_mem hi,
      coe_completedFreeBoltzmannWeight_insertOccupation_of_not_mem ε β hi]
    simp only [smul_smul]
    congr 1
    ring

/-- Trace-class-free annihilation intertwining for the bounded free heat operator:
`Kβ aᵢ = exp (β εᵢ) aᵢ Kβ`. -/
theorem completedFreeHeatOperator_comp_annihilate
    (ε : Mode → ℝ) (β : ℝ) (hbounded : CompletedFreeHeatBounded ε β) (i : Mode) :
    (completedFreeHeatOperator ε β hbounded).comp (completedAnnihilate i) =
      Complex.exp ((β : ℂ) * (ε i : ℂ)) •
        ((completedAnnihilate i).comp (completedFreeHeatOperator ε β hbounded)) := by
  apply Common.continuousLinearMap_ext_completedBasis
  intro n
  change
    completedFreeHeatOperator ε β hbounded
        (completedAnnihilate i (completedBasisState n)) =
      Complex.exp ((β : ℂ) * (ε i : ℂ)) •
        completedAnnihilate i
          (completedFreeHeatOperator ε β hbounded (completedBasisState n))
  by_cases hi : i ∈ n
  · rw [completedAnnihilate_basisState_of_mem hi, map_smul,
      completedFreeHeatOperator_apply_basis,
      completedFreeHeatOperator_apply_basis, map_smul,
      completedAnnihilate_basisState_of_mem hi,
      coe_completedFreeBoltzmannWeight_removeOccupation_of_mem ε β hi]
    simp only [smul_smul]
    congr 1
    ring
  · rw [completedAnnihilate_basisState_of_not_mem hi, map_zero,
      completedFreeHeatOperator_apply_basis, map_smul,
      completedAnnihilate_basisState_of_not_mem hi]
    simp

end
end Fermionic
end SecondQuantization
