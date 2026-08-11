import LeanCondensedMatter.Combinatorics.PerfectPairing.ExchangeSum
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion.Pairing
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.NumberConservingPairValue

set_option linter.style.header false

/-!
# Determinant form of the free quartic Wick expansion

For a fixed sequence of quartic vertex labels and imaginary times, the free fermionic Gibbs
expectation is an exchange-weighted sum over all perfect pairings. Number conservation kills the
creator--creator contractions, so the generic exchange-sum backend reduces that pairing sum to a
permutation sum; at fermionic exchange scalar `ζ = -1`, that permutation sum is a determinant.

Only the final physics-facing determinant identity is public. The intermediate pairing-sum
specialization and the flat creator--creator selection rule remain implementation details.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

private theorem flatVertexLegPairValue_quarticCreatorLeg_quarticCreatorLeg
    (ε : Mode → ℝ) (β : ℝ) {n : ℕ} (q : Fin n → QuarticVertexLabel Mode)
    (τ : Fin n → ℝ) (i i' : Fin (2 * n)) :
    flatVertexLegPairValue ε β q τ
      (quarticCreatorLeg n i) (quarticCreatorLeg n i') = 0 := by
  obtain ⟨c, mo, hc⟩ := exists_quarticLegOperatorForSequence_quarticCreatorLeg ε q τ i
  obtain ⟨c', mo', hc'⟩ := exists_quarticLegOperatorForSequence_quarticCreatorLeg ε q τ i'
  rw [flatVertexLegPairValue, hc, hc', LinearMap.smul_comp, LinearMap.comp_smul, smul_smul,
    Common.finiteHilbertOperator_smul, map_smul, smul_eq_mul,
    freeGibbsDensityOperator_expectation_create_comp_create, mul_zero]

private theorem sum_flatVertexLegPairingEvaluation_eq_det
    (ε : Mode → ℝ) (β : ℝ) (n : ℕ) (q : Fin n → QuarticVertexLabel Mode)
    (τ : Fin n → ℝ) :
    (∑ pairing : Pairing (2 * n), flatVertexLegPairingEvaluation ε β q τ pairing) =
      sideSplittingWeight (-1 : ℂ) (quarticLegSideSplitting n) *
        (exchangeMatrix (-1 : ℂ) (quarticLegSideSplitting n)
          (flatVertexLegPairValue ε β q τ)).det := by
  calc
    (∑ pairing : Pairing (2 * n), flatVertexLegPairingEvaluation ε β q τ pairing) =
        Combinatorics.pairingSum (-1 : ℂ) (flatVertexLegPairValue ε β q τ) := by
      rw [Combinatorics.pairingSum]
      exact Finset.sum_congr rfl fun pairing _ => by
        simp only [flatVertexLegPairingEvaluation,
          Common.BlochDeDominicis.Pairing.weight_fermion]
    _ = sideSplittingWeight (-1 : ℂ) (quarticLegSideSplitting n) *
          permutationSum (-1 : ℂ)
            (exchangeMatrix (-1 : ℂ) (quarticLegSideSplitting n)
              (flatVertexLegPairValue ε β q τ)) := by
      apply pairingSum_eq_permutationSum_of_inl_vanishing
      · norm_num
      · intro i i'
        simp only [quarticLegSideSplitting_inl]
        exact flatVertexLegPairValue_quarticCreatorLeg_quarticCreatorLeg ε β q τ i i'
    _ = sideSplittingWeight (-1 : ℂ) (quarticLegSideSplitting n) *
          (exchangeMatrix (-1 : ℂ) (quarticLegSideSplitting n)
            (flatVertexLegPairValue ε β q τ)).det := by
      rw [permutationSum_neg_one_eq_det]

/-- **Determinant form of the free quartic Wick theorem.** For a fixed sequence of quartic vertex
labels and imaginary times, the free Gibbs expectation of the ordered product is the determinant of
the generic fermionic exchange matrix, up to the global factor fixed by the creator/annihilator side
splitting. -/
theorem freeGibbsDensityOperator_expectation_nestedVertexOperatorComp_eq_det
    (ε : Mode → ℝ) (β : ℝ) (n : ℕ) (q : Fin n → QuarticVertexLabel Mode)
    (τ : Fin n → ℝ) :
    (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperator (nestedVertexOperatorComp ε n q τ)) =
      sideSplittingWeight (-1 : ℂ) (quarticLegSideSplitting n) *
        (exchangeMatrix (-1 : ℂ) (quarticLegSideSplitting n)
          (flatVertexLegPairValue ε β q τ)).det := by
  rw [freeGibbsDensityOperator_expectation_nestedVertexOperatorComp_eq_sum_pairingEvaluation,
    sum_flatVertexLegPairingEvaluation_eq_det]

end Fermionic
end SecondQuantization
