import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Core
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.FreeGibbs

set_option linter.style.header false

/-!
# Free-Gibbs intertwining with completed fermionic ladder operators

This file records the first KMS-facing product identities for the completed fermionic
representation.  The free Gibbs state is the generic pure-point Gibbs density operator specialized
to the completed occupation basis and `fermionEnergy ε`, while creation and annihilation are bounded
continuous linear maps.  Their products are therefore honest bounded-operator compositions; no
formal exponential of the unbounded free Hamiltonian is formed.

The occupation Boltzmann weight changes by the expected one-mode factor when a mode is inserted or
removed.  Consequently the normalized completed Gibbs density operator satisfies

`ρβ aᵢ† = exp (-β εᵢ) aᵢ† ρβ`

and

`ρβ aᵢ = exp (β εᵢ) aᵢ ρβ`.

These are the bounded thermal-intertwining identities needed before deriving completed-space KMS
cyclicity and the representation-specific `ExpectationPairingRecursion` bridge.
-/

namespace SecondQuantization
namespace Fermionic

open QuantumTheory

noncomputable section

variable {Mode : Type*} [LinearOrder Mode]

private theorem completedFreeGibbsProbability_insertOccupation_of_not_mem
    (ε : Mode → ℝ) (β : ℝ) {i : Mode} {n : Occupation Mode} (hi : i ∉ n) :
    purePointGibbsProbability (fermionEnergy ε) β (insertOccupation i n) =
      Real.exp (-β * ε i) * purePointGibbsProbability (fermionEnergy ε) β n := by
  have hweight :
      purePointBoltzmannWeight (fermionEnergy ε) β (insertOccupation i n) =
        Real.exp (-β * ε i) * purePointBoltzmannWeight (fermionEnergy ε) β n := by
    change Real.exp (-β * fermionEnergy ε (insertOccupation i n)) =
      Real.exp (-β * ε i) * Real.exp (-β * fermionEnergy ε n)
    simp only [fermionEnergy, insertOccupation, Finset.sum_insert hi]
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [purePointGibbsProbability, hweight]
  ring

private theorem completedFreeGibbsProbability_removeOccupation_of_mem
    (ε : Mode → ℝ) (β : ℝ) {i : Mode} {n : Occupation Mode} (hi : i ∈ n) :
    purePointGibbsProbability (fermionEnergy ε) β (removeOccupation i n) =
      Real.exp (β * ε i) * purePointGibbsProbability (fermionEnergy ε) β n := by
  have henergy :
      fermionEnergy ε n = fermionEnergy ε (removeOccupation i n) + ε i := by
    simpa [fermionEnergy, removeOccupation] using (Finset.sum_erase_add n ε hi).symm
  have hweight :
      purePointBoltzmannWeight (fermionEnergy ε) β (removeOccupation i n) =
        Real.exp (β * ε i) * purePointBoltzmannWeight (fermionEnergy ε) β n := by
    change Real.exp (-β * fermionEnergy ε (removeOccupation i n)) =
      Real.exp (β * ε i) * Real.exp (-β * fermionEnergy ε n)
    rw [henergy, ← Real.exp_add]
    congr 1
    ring
  simp only [purePointGibbsProbability, hweight]
  ring

/-- Complex form of the free Gibbs insertion ratio, matching the scalar used in operator identities. -/
theorem coe_completedFreeGibbsProbability_insertOccupation_of_not_mem
    (ε : Mode → ℝ) (β : ℝ) {i : Mode} {n : Occupation Mode} (hi : i ∉ n) :
    (purePointGibbsProbability (fermionEnergy ε) β (insertOccupation i n) : ℂ) =
      Complex.exp (-(β : ℂ) * (ε i : ℂ)) *
        (purePointGibbsProbability (fermionEnergy ε) β n : ℂ) := by
  rw [completedFreeGibbsProbability_insertOccupation_of_not_mem ε β hi]
  push_cast
  rfl

/-- Complex form of the free Gibbs removal ratio, matching the scalar used in operator identities. -/
theorem coe_completedFreeGibbsProbability_removeOccupation_of_mem
    (ε : Mode → ℝ) (β : ℝ) {i : Mode} {n : Occupation Mode} (hi : i ∈ n) :
    (purePointGibbsProbability (fermionEnergy ε) β (removeOccupation i n) : ℂ) =
      Complex.exp ((β : ℂ) * (ε i : ℂ)) *
        (purePointGibbsProbability (fermionEnergy ε) β n : ℂ) := by
  rw [completedFreeGibbsProbability_removeOccupation_of_mem ε β hi]
  push_cast
  rfl

omit [LinearOrder Mode] in
/-- Two bounded operators on completed Fock space are equal when they agree on every occupation
basis vector.  The proof passes through the dense algebraic finite-support core. -/
private theorem continuousLinearMap_ext_completedBasis
    {A B : CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode}
    (h : ∀ n : Occupation Mode,
      A.toLinearMap (completedBasisState n) = B.toLinearMap (completedBasisState n)) :
    A = B := by
  apply DFunLike.ext'
  exact (map_continuous A).ext_on algebraicToCompleted_denseRange (map_continuous B) <| by
    rintro _ ⟨x, rfl⟩
    have hcore :
        A.toLinearMap.comp algebraicToCompleted =
          B.toLinearMap.comp algebraicToCompleted := by
      apply Finsupp.lhom_ext
      intro n c
      have hc : (Finsupp.single n c : OccupationFock Mode) = c • basisState n :=
        (Finsupp.smul_single_one n c).symm
      rw [hc]
      simp only [LinearMap.comp_apply, map_smul, algebraicToCompleted_basisState]
      rw [h n]
    exact congrArg (fun f : OccupationFock Mode →ₗ[ℂ] CompletedFockSpace Mode => f x) hcore

/-- Completed free-Gibbs creation intertwining:
`ρβ aᵢ† = exp (-β εᵢ) aᵢ† ρβ` as an identity of bounded operators. -/
theorem completedFreeGibbsDensityOperator_comp_create
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β) (i : Mode) :
    (purePointGibbsDensityOperator completedOccupationHilbertBasis
        (fermionEnergy ε) β hsum).op.comp (completedCreate i) =
      Complex.exp (-(β : ℂ) * (ε i : ℂ)) •
        ((completedCreate i).comp
          (purePointGibbsDensityOperator completedOccupationHilbertBasis
            (fermionEnergy ε) β hsum).op) := by
  apply continuousLinearMap_ext_completedBasis
  intro n
  change
    (purePointGibbsDensityOperator completedOccupationHilbertBasis
      (fermionEnergy ε) β hsum).op
        (completedCreate i (completedBasisState n)) =
      Complex.exp (-(β : ℂ) * (ε i : ℂ)) •
        completedCreate i
          ((purePointGibbsDensityOperator completedOccupationHilbertBasis
            (fermionEnergy ε) β hsum).op (completedBasisState n))
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
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β) (i : Mode) :
    (purePointGibbsDensityOperator completedOccupationHilbertBasis
        (fermionEnergy ε) β hsum).op.comp (completedAnnihilate i) =
      Complex.exp ((β : ℂ) * (ε i : ℂ)) •
        ((completedAnnihilate i).comp
          (purePointGibbsDensityOperator completedOccupationHilbertBasis
            (fermionEnergy ε) β hsum).op) := by
  apply continuousLinearMap_ext_completedBasis
  intro n
  change
    (purePointGibbsDensityOperator completedOccupationHilbertBasis
      (fermionEnergy ε) β hsum).op
        (completedAnnihilate i (completedBasisState n)) =
      Complex.exp ((β : ℂ) * (ε i : ℂ)) •
        completedAnnihilate i
          ((purePointGibbsDensityOperator completedOccupationHilbertBasis
            (fermionEnergy ε) β hsum).op (completedBasisState n))
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
