import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion.Flattening
import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonVertexMoment
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeBoltzmannCore
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsDensityOperator
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsExpectationBridge
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Induction

set_option linter.style.header false

/-!
# Dyson diagram expansion: density-state pairing
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

/-! ## Applying the general theorem to the flattened `4n`-leg family -/

omit [DecidableEq Mode] [LinearOrder Mode] in
/-- **The free partition function's un-normalized trace is nonzero** — the general theorem's `hZ`
hypothesis, bridged from `freePartitionFunction_ne_zero` via
`Common.traceFock_diagonalEvolution_eq_weightSum` and a direct identification of the Common and
free Boltzmann weights. -/
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

/-- The canonical finite Gibbs expectation of `nestedVertexOperatorComp` is the pairing sum
obtained by applying the general finite Bloch–de Dominicis theorem to the flattened `4n`-leg
family. -/
private theorem finiteGibbsExpectation_nestedVertexOperatorComp_eq_sum_pairing
    (ε : Mode → ℝ) (β : ℝ)
    (n : ℕ) (q : Fin n → QuarticVertexLabel Mode) (τ : Fin n → ℝ) :
    Common.finiteGibbsExpectation (fermionEnergy ε) β (nestedVertexOperatorComp ε n q τ) =
      ∑ pairing : Combinatorics.Pairing (2 * n),
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

/-- The nested quartic vertex product satisfies the pairing expansion through the canonical free
Gibbs density-state expectation. -/
theorem freeGibbsDensityOperator_expectation_nestedVertexOperatorComp_eq_sum_pairing
    (ε : Mode → ℝ) (β : ℝ) (n : ℕ) (q : Fin n → QuarticVertexLabel Mode)
    (τ : Fin n → ℝ) :
    (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperator (nestedVertexOperatorComp ε n q τ)) =
      ∑ pairing : Combinatorics.Pairing (2 * n),
        pairing.weight Common.Statistics.fermion *
          ∏ pr ∈ pairing.pairs,
            (freeGibbsDensityOperator ε β).expectation
              (Common.finiteHilbertOperator
                ((quarticLegOperatorForSequence ε q τ pr.1).comp
                  (quarticLegOperatorForSequence ε q τ pr.2))) := by
  simpa only [freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation] using
    finiteGibbsExpectation_nestedVertexOperatorComp_eq_sum_pairing ε β n q τ

/-! ## Integrating the pairing sum over the ordered simplex -/

private theorem finiteGibbsExpectation_smul_apply (ε : Mode → ℝ) (β : ℝ) (c : ℂ)
    (A : FockSpace Mode →ₗ[ℂ] FockSpace Mode) :
    Common.finiteGibbsExpectation (fermionEnergy ε) β (c • A) =
      c * Common.finiteGibbsExpectation (fermionEnergy ε) β A := by
  change (Common.finiteGibbsExpectationLinearMap (fermionEnergy ε) β) (c • A) =
    c * (Common.finiteGibbsExpectationLinearMap (fermionEnergy ε) β) A
  rw [map_smul, smul_eq_mul]

/-- **A pair value of two flattened leg operators, in closed form**: unfolds both legs to their
`Complex.exp` eigenvalue-shift form (`quarticLegOperatorForSequence_eq_smul`) and pulls both
scalars out of `Common.finiteGibbsExpectation` (`finiteGibbsExpectation_smul_apply`), leaving a
fixed (`τ`-independent) pair value of the two *bare* local-leg operators — the
`quarticLegOperatorForSequence` analogue of `WickDiagram/Amplitude.lean`'s
`orderedQuarticPairValue_eq`. -/
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
    LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, finiteGibbsExpectation_smul_apply]

/-- A pair of evolved flattened legs has the expected exponential prefactor through the canonical
free Gibbs density-state expectation. -/
theorem freeGibbsDensityOperator_expectation_quarticLegOperatorForSequence_pair_eq
    {n : ℕ} (ε : Mode → ℝ) (β : ℝ) (q : Fin n → QuarticVertexLabel Mode)
    (τ : Fin n → ℝ) (a b : Fin (2 * (2 * n))) :
    (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperator
          ((quarticLegOperatorForSequence ε q τ a).comp
            (quarticLegOperatorForSequence ε q τ b))) =
      Complex.exp ((τ (flatVertexIndex n a) * flatVertexLegEnergyShift ε q a : ℝ) : ℂ) *
        Complex.exp ((τ (flatVertexIndex n b) * flatVertexLegEnergyShift ε q b : ℝ) : ℂ) *
        (freeGibbsDensityOperator ε β).expectation
          (Common.finiteHilbertOperator
            ((quarticLocalLegOperator (q (flatVertexIndex n a)) (flatLocalLeg n a)).comp
              (quarticLocalLegOperator (q (flatVertexIndex n b)) (flatLocalLeg n b)))) := by
  simpa only [freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation] using
    finiteGibbsExpectation_quarticLegOperatorForSequence_pair_eq ε β q τ a b

/-- **A pair value of two flattened leg operators is continuous in the time assignment `τ`** —
directly from the closed form `finiteGibbsExpectation_quarticLegOperatorForSequence_pair_eq`: a
product of two `Complex.exp`s of a continuous (coordinate-linear) function of `τ`, times a
`τ`-independent constant. -/
private theorem continuous_finiteGibbsExpectation_quarticLegOperatorForSequence_pair {n : ℕ}
    (ε : Mode → ℝ)
    (β : ℝ) (q : Fin n → QuarticVertexLabel Mode) (a b : Fin (2 * (2 * n))) :
    Continuous (fun τ : Fin n → ℝ => Common.finiteGibbsExpectation (fermionEnergy ε) β
      ((quarticLegOperatorForSequence ε q τ a).comp (quarticLegOperatorForSequence ε q τ b))) := by
  simp only [finiteGibbsExpectation_quarticLegOperatorForSequence_pair_eq]
  fun_prop

/-- The canonical density-state pair value is continuous in the vertex-time assignment. -/
theorem continuous_freeGibbsDensityOperator_expectation_quarticLegOperatorForSequence_pair
    {n : ℕ} (ε : Mode → ℝ) (β : ℝ) (q : Fin n → QuarticVertexLabel Mode)
    (a b : Fin (2 * (2 * n))) :
    Continuous (fun τ : Fin n → ℝ =>
      (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperator
          ((quarticLegOperatorForSequence ε q τ a).comp
            (quarticLegOperatorForSequence ε q τ b)))) := by
  simpa only [freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation] using
    continuous_finiteGibbsExpectation_quarticLegOperatorForSequence_pair ε β q a b

/-- **A pairing's contraction term is continuous in `τ`** — a `τ`-independent crossing-sign
constant, times a finite product (over the pairing's pairs) of
`continuous_finiteGibbsExpectation_quarticLegOperatorForSequence_pair`'s continuous pair values. -/
private theorem continuous_finiteGibbsExpectation_flatVertexLegPairingTerm {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ)
    (q : Fin n → QuarticVertexLabel Mode)
    (pairing : Combinatorics.Pairing (2 * n)) :
    Continuous (fun τ : Fin n → ℝ => pairing.weight Common.Statistics.fermion *
      ∏ pr ∈ pairing.pairs, Common.finiteGibbsExpectation (fermionEnergy ε) β
        ((quarticLegOperatorForSequence ε q τ pr.1).comp
          (quarticLegOperatorForSequence ε q τ pr.2))) :=
  continuous_const.mul (continuous_finsetProd _ fun pr _ =>
    continuous_finiteGibbsExpectation_quarticLegOperatorForSequence_pair ε β q pr.1 pr.2)

/-- A pairing's canonical density-state contraction term is continuous in the vertex-time
assignment. -/
theorem continuous_flatVertexLegPairingTerm {n : ℕ} (ε : Mode → ℝ) (β : ℝ)
    (q : Fin n → QuarticVertexLabel Mode)
    (pairing : Combinatorics.Pairing (2 * n)) :
    Continuous (fun τ : Fin n → ℝ => pairing.weight Common.Statistics.fermion *
      ∏ pr ∈ pairing.pairs,
        (freeGibbsDensityOperator ε β).expectation
          (Common.finiteHilbertOperator
            ((quarticLegOperatorForSequence ε q τ pr.1).comp
              (quarticLegOperatorForSequence ε q τ pr.2)))) :=
  continuous_const.mul (continuous_finsetProd _ fun pr _ =>
    continuous_freeGibbsDensityOperator_expectation_quarticLegOperatorForSequence_pair
      ε β q pr.1 pr.2)

/-- **The ordered-simplex integral of the finite Gibbs expectation of
`nestedVertexOperatorComp`, as a sum over pairings of integrated contraction terms** — rewrites
the integrand pointwise via `finiteGibbsExpectation_nestedVertexOperatorComp_eq_sum_pairing`
(`intervalIntegral.orderedSimplexIntegral_congr`), pulls the finite `Pairing (2 * n)` sum out past
the integral (`intervalIntegral.orderedSimplexIntegral_finsetSum`, using
`continuous_finiteGibbsExpectation_flatVertexLegPairingTerm` for its integrability side condition),
then pulls each pairing's `τ`-independent weight back out of its own integral
(`intervalIntegral.orderedSimplexIntegral_smul`). -/
private theorem
    finiteGibbsExpectation_orderedSimplexIntegral_nestedVertexOperatorComp_eq_sum_pairing
    (ε : Mode → ℝ) (β t : ℝ) (n : ℕ) (q : Fin n → QuarticVertexLabel Mode) :
    intervalIntegral.orderedSimplexIntegral n t
        (fun τ => Common.finiteGibbsExpectation (fermionEnergy ε) β
          (nestedVertexOperatorComp ε n q τ)) =
      ∑ pairing : Combinatorics.Pairing (2 * n),
        pairing.weight Common.Statistics.fermion *
          intervalIntegral.orderedSimplexIntegral n t
            (fun τ => ∏ pr ∈ pairing.pairs,
              Common.finiteGibbsExpectation (fermionEnergy ε) β
                ((quarticLegOperatorForSequence ε q τ pr.1).comp
                  (quarticLegOperatorForSequence ε q τ pr.2))) := by
  rw [intervalIntegral.orderedSimplexIntegral_congr
      (fun τ => finiteGibbsExpectation_nestedVertexOperatorComp_eq_sum_pairing ε β n q τ),
    intervalIntegral.orderedSimplexIntegral_finsetSum _ n t _
      (fun pairing _ => continuous_finiteGibbsExpectation_flatVertexLegPairingTerm ε β q pairing)]
  exact Finset.sum_congr rfl fun pairing _ =>
    intervalIntegral.orderedSimplexIntegral_smul n t _ _

/-- The ordered-simplex integral of the canonical density-state nested-vertex expectation is the
sum of the integrated canonical density-state pairing products. -/
theorem orderedSimplexIntegral_freeGibbsDensityOperator_expectation_nestedVertexOperatorComp_eq_sum_pairing
    (ε : Mode → ℝ) (β t : ℝ) (n : ℕ) (q : Fin n → QuarticVertexLabel Mode) :
    intervalIntegral.orderedSimplexIntegral n t
        (fun τ => (freeGibbsDensityOperator ε β).expectation
          (Common.finiteHilbertOperator (nestedVertexOperatorComp ε n q τ))) =
      ∑ pairing : Combinatorics.Pairing (2 * n),
        pairing.weight Common.Statistics.fermion *
          intervalIntegral.orderedSimplexIntegral n t
            (fun τ => ∏ pr ∈ pairing.pairs,
              (freeGibbsDensityOperator ε β).expectation
                (Common.finiteHilbertOperator
                  ((quarticLegOperatorForSequence ε q τ pr.1).comp
                    (quarticLegOperatorForSequence ε q τ pr.2)))) := by
  simpa only [freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation] using
    finiteGibbsExpectation_orderedSimplexIntegral_nestedVertexOperatorComp_eq_sum_pairing
      ε β t n q

/-- **`dysonVertexMoment` of `quarticInteraction`, as a genuine sum over vertex-label sequences
and pairings through canonical free Gibbs density-state contractions.** The last remaining step is
reindexing this `(vertex-label sequence, pairing)` double sum into a sum over
`QuarticWickDiagram`s. -/
theorem dysonVertexMoment_quarticInteraction_eq_sum_vertexLabel_pairing {α : Type*}
    [DecidableEq α] (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) (S : Finset α) :
    dysonVertexMoment ε β (quarticInteraction g) S =
      (S.card.factorial : ℂ) * (-1 : ℂ) ^ S.card *
        ∑ q : Fin S.card → QuarticVertexLabel Mode, (∏ i, g (q i)) *
          ∑ pairing : Combinatorics.Pairing (2 * S.card),
            pairing.weight Common.Statistics.fermion *
              intervalIntegral.orderedSimplexIntegral S.card β (fun τ =>
                ∏ pr ∈ pairing.pairs,
                  (freeGibbsDensityOperator ε β).expectation
                    (Common.finiteHilbertOperator
                      ((quarticLegOperatorForSequence ε q τ pr.1).comp
                        (quarticLegOperatorForSequence ε q τ pr.2)))) := by
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
        ∑ pairing : Combinatorics.Pairing (2 * S.card),
          pairing.weight Common.Statistics.fermion *
            intervalIntegral.orderedSimplexIntegral S.card β
              (fun τ => ∏ pr ∈ pairing.pairs,
                (freeGibbsDensityOperator ε β).expectation
                  (Common.finiteHilbertOperator
                    ((quarticLegOperatorForSequence ε q τ pr.1).comp
                      (quarticLegOperatorForSequence ε q τ pr.2)))) :=
    Finset.sum_congr rfl fun q _ => by
      rw [
        orderedSimplexIntegral_freeGibbsDensityOperator_expectation_nestedVertexOperatorComp_eq_sum_pairing
      ]
  rw [dysonVertexMoment_eq_freeGibbsDensityOperator_expectation, hkey, mul_assoc, hsum]

end Fermionic
end SecondQuantization
