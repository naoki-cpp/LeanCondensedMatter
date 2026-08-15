import LeanCondensedMatter.Combinatorics.PerfectPairing.Evaluation
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion.Flattening
import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonVertexMoment
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeBoltzmannCore
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsDensityOperator
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsExpectationBridge
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Induction

set_option linter.style.header false

/-!
# Dyson diagram expansion: canonical pairing evaluation

The finite Bloch--de Dominicis calculation remains private coordinate proof infrastructure. Public
Dyson pairing statements are expressed through the combinatorics-owned `Pairing.evaluation` boundary
with the canonical free Gibbs density-state pair kernel.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-! ## Applying the general theorem to the flattened `4n`-leg family -/

omit [LinearOrder Mode] in
private theorem traceFock_diagonalEvolution_fermionEnergy_ne_zero (ε : Mode → ℝ) (β : ℝ) :
    Common.traceFock (Common.diagonalEvolution (fermionEnergy ε) (-β)) ≠ 0 := by
  rw [Common.traceFock_diagonalEvolution_eq_weightSum]
  have hw : Common.boltzmannWeight (fermionEnergy ε) β = freeBoltzmannWeight ε β := by
    funext m
    rw [Common.boltzmannWeight, freeBoltzmannWeight, fermionEnergy]
    push_cast
    ring_nf
  rw [hw]
  exact freePartitionFunction_ne_zero ε β

private theorem finiteGibbsExpectation_nestedVertexOperatorComp_eq_sum_pairing
    (ε : Mode → ℝ) (β : ℝ)
    (n : ℕ) (q : Fin n → QuarticVertexLabel Mode) (τ : Fin n → ℝ) :
    Common.finiteGibbsExpectation (fermionEnergy ε) β (nestedVertexOperatorComp ε n q τ) =
      ∑ pairing : Pairing (2 * n),
        pairing.weight Common.Statistics.fermion *
          ∏ pr ∈ pairing.pairs, Common.finiteGibbsExpectation (fermionEnergy ε) β
            ((quarticLegOperatorForSequence ε q τ pr.1).comp
              (quarticLegOperatorForSequence ε q τ pr.2)) := by
  have hgen :=
    Common.BlochDeDominicis.finiteGibbsExpectation_prodComp_eq_sum_pairing
      Common.Statistics.fermion (fermionEnergy ε) β
      (traceFock_diagonalEvolution_fermionEnergy_ne_zero ε β) (2 * n)
      (quarticLegOperatorForSequence ε q τ) (flatVertexLegEnergyShift ε q)
      (flatVertexLegCommutatorCoeff ε q τ)
      (fun p => heisenbergEvolve_quarticLegOperatorForSequence ε β q τ p)
      (fun i j _ => zetaCommutator_quarticLegOperatorForSequence ε q τ i j)
      (fun i => one_sub_zetaInt_fermion_mul_exp_flatVertexLegEnergyShift_ne_zero ε β q i)
  rw [← prodComp_ofFn_quarticLegOperatorForSequence_eq_nestedVertexOperatorComp]
  exact hgen

/-- Canonical free Gibbs density-state contraction of two flattened quartic Dyson legs. -/
noncomputable def flatVertexLegPairValue {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (q : Fin n → QuarticVertexLabel Mode)
    (τ : Fin n → ℝ) (a b : Fin (2 * (2 * n))) : ℂ :=
  (freeGibbsDensityOperator ε β).expectation
    (Common.finiteHilbertOperator
      ((quarticLegOperatorForSequence ε q τ a).comp
        (quarticLegOperatorForSequence ε q τ b)))

/-- Canonical scalar value of a flattened-leg pairing. -/
noncomputable def flatVertexLegPairingEvaluation {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (q : Fin n → QuarticVertexLabel Mode)
    (τ : Fin n → ℝ) (pairing : Pairing (2 * n)) : ℂ :=
  pairing.evaluation (pairing.weight Common.Statistics.fermion)
    (flatVertexLegPairValue ε β q τ)

@[simp]
theorem flatVertexLegPairingEvaluation_eq {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (q : Fin n → QuarticVertexLabel Mode)
    (τ : Fin n → ℝ) (pairing : Pairing (2 * n)) :
    flatVertexLegPairingEvaluation ε β q τ pairing =
      pairing.weight Common.Statistics.fermion *
        ∏ pr ∈ pairing.pairs, flatVertexLegPairValue ε β q τ pr.1 pr.2 :=
  rfl

private theorem nestedVertexExpectation_eq_pairingSum
    (ε : Mode → ℝ) (β : ℝ) (n : ℕ) (q : Fin n → QuarticVertexLabel Mode)
    (τ : Fin n → ℝ) :
    (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperator (nestedVertexOperatorComp ε n q τ)) =
      ∑ pairing : Pairing (2 * n),
        flatVertexLegPairingEvaluation ε β q τ pairing := by
  simpa only [flatVertexLegPairingEvaluation, Combinatorics.Pairing.evaluation, flatVertexLegPairValue,
    freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation] using
    finiteGibbsExpectation_nestedVertexOperatorComp_eq_sum_pairing ε β n q τ

/-! ## Pair-kernel regularity -/

private theorem finiteGibbsExpectation_quarticLegOperatorForSequence_pair_eq {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (τ : Fin n → ℝ) (a b : Fin (2 * (2 * n))) :
    Common.finiteGibbsExpectation (fermionEnergy ε) β
        ((quarticLegOperatorForSequence ε q τ a).comp (quarticLegOperatorForSequence ε q τ b)) =
      Complex.exp ((τ (flatVertexIndex n a) * flatVertexLegEnergyShift ε q a : ℝ) : ℂ) *
        Complex.exp ((τ (flatVertexIndex n b) * flatVertexLegEnergyShift ε q b : ℝ) : ℂ) *
        Common.finiteGibbsExpectation (fermionEnergy ε) β
          ((quarticLocalLegOperator (q (flatVertexIndex n a)) (flatLocalLeg n a)).comp
            (quarticLocalLegOperator (q (flatVertexIndex n b)) (flatLocalLeg n b))) := by
  rw [quarticLegOperatorForSequence_eq_smul, quarticLegOperatorForSequence_eq_smul,
    LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, Common.finiteGibbsExpectation_smul]

/-- Closed form of the canonical flattened-leg pair kernel. -/
theorem flatVertexLegPairValue_eq {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (q : Fin n → QuarticVertexLabel Mode)
    (τ : Fin n → ℝ) (a b : Fin (2 * (2 * n))) :
    flatVertexLegPairValue ε β q τ a b =
      Complex.exp ((τ (flatVertexIndex n a) * flatVertexLegEnergyShift ε q a : ℝ) : ℂ) *
        Complex.exp ((τ (flatVertexIndex n b) * flatVertexLegEnergyShift ε q b : ℝ) : ℂ) *
        (freeGibbsDensityOperator ε β).expectation
          (Common.finiteHilbertOperator
            ((quarticLocalLegOperator (q (flatVertexIndex n a)) (flatLocalLeg n a)).comp
              (quarticLocalLegOperator (q (flatVertexIndex n b)) (flatLocalLeg n b)))) := by
  simpa only [flatVertexLegPairValue,
    freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation] using
    finiteGibbsExpectation_quarticLegOperatorForSequence_pair_eq ε β q τ a b

/-- The canonical flattened-leg pair kernel is continuous in the vertex-time assignment. -/
theorem continuous_flatVertexLegPairValue {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (q : Fin n → QuarticVertexLabel Mode)
    (a b : Fin (2 * (2 * n))) :
    Continuous (fun τ : Fin n → ℝ => flatVertexLegPairValue ε β q τ a b) := by
  simp only [flatVertexLegPairValue_eq]
  fun_prop

/-- Canonical pairing evaluation is continuous in the vertex-time assignment. -/
theorem continuous_flatVertexLegPairingEvaluation {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (q : Fin n → QuarticVertexLabel Mode)
    (pairing : Pairing (2 * n)) :
    Continuous (fun τ : Fin n → ℝ => flatVertexLegPairingEvaluation ε β q τ pairing) := by
  simp only [flatVertexLegPairingEvaluation, Combinatorics.Pairing.evaluation]
  exact continuous_const.mul (continuous_finsetProd _ fun pr _ =>
    continuous_flatVertexLegPairValue ε β q pr.1 pr.2)

/-! ## Integrating the pairing sum over the ordered simplex -/

private theorem orderedSimplexIntegral_nestedVertexExpectation_eq_pairingSum
    (ε : Mode → ℝ) (β t : ℝ) (n : ℕ) (q : Fin n → QuarticVertexLabel Mode) :
    intervalIntegral.orderedSimplexIntegral n t
        (fun τ => (freeGibbsDensityOperator ε β).expectation
          (Common.finiteHilbertOperator (nestedVertexOperatorComp ε n q τ))) =
      ∑ pairing : Pairing (2 * n),
        intervalIntegral.orderedSimplexIntegral n t
          (fun τ => flatVertexLegPairingEvaluation ε β q τ pairing) := by
  rw [intervalIntegral.orderedSimplexIntegral_congr
      (fun τ => nestedVertexExpectation_eq_pairingSum ε β n q τ),
    intervalIntegral.orderedSimplexIntegral_finsetSum _ n t _
      (fun pairing _ => continuous_flatVertexLegPairingEvaluation ε β q pairing)]

/-- `dysonVertexMoment` of the quartic interaction in the canonical pairing-evaluator presentation. -/
theorem dysonVertexMoment_quarticInteraction_eq_sum_vertexLabel_pairingEvaluation {α : Type*}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) (S : Finset α) :
    dysonVertexMoment ε β (quarticInteraction g) S =
      (S.card.factorial : ℂ) * (-1 : ℂ) ^ S.card *
        ∑ q : Fin S.card → QuarticVertexLabel Mode, (∏ i, g (q i)) *
          ∑ pairing : Pairing (2 * S.card),
            intervalIntegral.orderedSimplexIntegral S.card β
              (fun τ => flatVertexLegPairingEvaluation ε β q τ pairing) := by
  classical
  have hkey :=
    freeGibbsDensityOperator_expectation_comp_dysonCoeff_quarticInteraction
      ε β g S.card β LinearMap.id
  simp only [LinearMap.id_comp] at hkey
  have hsum :
      ∑ q : Fin S.card → QuarticVertexLabel Mode, (∏ i, g (q i)) *
        intervalIntegral.orderedSimplexIntegral S.card β
          (fun τ => (freeGibbsDensityOperator ε β).expectation
            (Common.finiteHilbertOperator
              (nestedVertexOperatorComp ε S.card q τ))) =
      ∑ q : Fin S.card → QuarticVertexLabel Mode, (∏ i, g (q i)) *
        ∑ pairing : Pairing (2 * S.card),
          intervalIntegral.orderedSimplexIntegral S.card β
            (fun τ => flatVertexLegPairingEvaluation ε β q τ pairing) :=
    Finset.sum_congr rfl fun q _ => by
      rw [orderedSimplexIntegral_nestedVertexExpectation_eq_pairingSum]
  rw [dysonVertexMoment_eq_freeGibbsDensityOperator_expectation, hkey, mul_assoc, hsum]

end Fermionic
end SecondQuantization
