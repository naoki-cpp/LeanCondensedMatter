import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion.Flattening

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
`Common.traceFock_diagonalEvolution_eq_weightSum` and
`freeBoltzmannWeight_eq_boltzmannWeight_fermionEnergy`. -/
theorem traceFock_diagonalEvolution_fermionEnergy_ne_zero (ε : Mode → ℝ) (β : ℝ) :
    Common.traceFock (Common.diagonalEvolution (fermionEnergy ε) (-β)) ≠ 0 := by
  rw [Common.traceFock_diagonalEvolution_eq_weightSum]
  have hw : Common.boltzmannWeight (fermionEnergy ε) β = freeBoltzmannWeight ε β :=
    funext fun m => (freeBoltzmannWeight_eq_boltzmannWeight_fermionEnergy ε β m).symm
  rw [hw]
  exact freePartitionFunction_ne_zero ε β

/-- **`nestedVertexOperatorComp`'s free Gibbs expectation, as the general theorem's pairing sum**
— applies `Common.BlochDeDominicis.finiteGibbsExpectation_prodComp_eq_sum_pairing` (at its own
`n := 2 * n`, matching `quarticLegOperatorForSequence`'s `Fin (2 * (2 * n))` domain exactly, with
no cast needed) to the flattened family `quarticLegOperatorForSequence ε q τ`, using
`heisenbergEvolve_quarticLegOperatorForSequence`, `zetaCommutator_quarticLegOperatorForSequence`,
and `one_sub_zetaInt_fermion_mul_exp_flatVertexLegEnergyShift_ne_zero` for its three hypotheses,
then bridges the conclusion from `Common.finiteGibbsExpectation` to `freeGibbsExpectation`
(`freeGibbsExpectation_eq_finiteGibbsExpectation`) and from `Common.prodComp (List.ofFn
(quarticLegOperatorForSequence ε q τ))` to `nestedVertexOperatorComp ε n q τ`
(`prodComp_ofFn_quarticLegOperatorForSequence_eq_nestedVertexOperatorComp`). This is all three of
the general theorem's hypotheses discharged and the theorem itself applied — the last purely
combinatorial step is reindexing the resulting `(vertex-label sequence, pairing)` sum into a sum
over `QuarticWickDiagram`s. -/
private theorem coordinate_expectation_nestedVertexOperatorComp_eq_sum_pairing (ε : Mode → ℝ) (β : ℝ)
    (n : ℕ) (q : Fin n → QuarticVertexLabel Mode) (τ : Fin n → ℝ) :
    freeGibbsExpectation ε β (nestedVertexOperatorComp ε n q τ) =
      ∑ pairing : Combinatorics.Pairing (2 * n),
        pairing.weight Common.Statistics.fermion *
          ∏ pr ∈ pairing.pairs, freeGibbsExpectation ε β
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
  rw [← prodComp_ofFn_quarticLegOperatorForSequence_eq_nestedVertexOperatorComp,
    freeGibbsExpectation_eq_finiteGibbsExpectation, hgen]
  refine Finset.sum_congr rfl fun pairing _ => ?_
  congr 1
  exact Finset.prod_congr rfl fun pr _ =>
    (freeGibbsExpectation_eq_finiteGibbsExpectation ε β _).symm

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
  simpa only [freeGibbsDensityOperator_expectation_eq_freeGibbsExpectation] using
    coordinate_expectation_nestedVertexOperatorComp_eq_sum_pairing ε β n q τ

/-! ## Integrating the pairing sum over the ordered simplex -/

/-- **A pair value of two flattened leg operators, in closed form**: unfolds both legs to their
`Complex.exp` eigenvalue-shift form (`quarticLegOperatorForSequence_eq_smul`) and pulls both
scalars out of `freeGibbsExpectation` (`freeGibbsExpectation_smul`), leaving a fixed
(`τ`-independent) pair value of the two *bare* local-leg operators — the
`quarticLegOperatorForSequence` analogue of `WickDiagram/Amplitude.lean`'s
`orderedQuarticPairValue_eq`. -/
private theorem coordinate_expectation_quarticLegOperatorForSequence_pair_eq {n : ℕ} (ε : Mode → ℝ) (β : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (τ : Fin n → ℝ) (a b : Fin (2 * (2 * n))) :
    freeGibbsExpectation ε β
        ((quarticLegOperatorForSequence ε q τ a).comp (quarticLegOperatorForSequence ε q τ b)) =
      Complex.exp ((τ (flatVertexIndex n a) * flatVertexLegEnergyShift ε q a : ℝ) : ℂ) *
        Complex.exp ((τ (flatVertexIndex n b) * flatVertexLegEnergyShift ε q b : ℝ) : ℂ) *
        freeGibbsExpectation ε β
          ((quarticLocalLegOperator (q (flatVertexIndex n a)) (flatLocalLeg n a)).comp
            (quarticLocalLegOperator (q (flatVertexIndex n b)) (flatLocalLeg n b))) := by
  rw [quarticLegOperatorForSequence_eq_smul, quarticLegOperatorForSequence_eq_smul,
    LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, freeGibbsExpectation_smul]

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
  simpa only [freeGibbsDensityOperator_expectation_eq_freeGibbsExpectation] using
    coordinate_expectation_quarticLegOperatorForSequence_pair_eq ε β q τ a b

/-- **A pair value of two flattened leg operators is continuous in the time assignment `τ`** —
directly from the closed form `coordinate_expectation_quarticLegOperatorForSequence_pair_eq`: a
product of two `Complex.exp`s of a continuous (coordinate-linear) function of `τ`, times a
`τ`-independent constant. -/
private theorem continuous_coordinate_expectation_quarticLegOperatorForSequence_pair {n : ℕ} (ε : Mode → ℝ)
    (β : ℝ) (q : Fin n → QuarticVertexLabel Mode) (a b : Fin (2 * (2 * n))) :
    Continuous (fun τ : Fin n → ℝ => freeGibbsExpectation ε β
      ((quarticLegOperatorForSequence ε q τ a).comp (quarticLegOperatorForSequence ε q τ b))) := by
  simp only [coordinate_expectation_quarticLegOperatorForSequence_pair_eq]
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
  simpa only [freeGibbsDensityOperator_expectation_eq_freeGibbsExpectation] using
    continuous_coordinate_expectation_quarticLegOperatorForSequence_pair ε β q a b

/-- **A pairing's contraction term is continuous in `τ`** — a `τ`-independent crossing-sign
constant, times a finite product (over the pairing's pairs) of
`continuous_coordinate_expectation_quarticLegOperatorForSequence_pair`'s continuous pair values. -/
private theorem continuous_coordinate_flatVertexLegPairingTerm {n : ℕ} (ε : Mode → ℝ) (β : ℝ)
    (q : Fin n → QuarticVertexLabel Mode)
    (pairing : Combinatorics.Pairing (2 * n)) :
    Continuous (fun τ : Fin n → ℝ => pairing.weight Common.Statistics.fermion *
      ∏ pr ∈ pairing.pairs, freeGibbsExpectation ε β
        ((quarticLegOperatorForSequence ε q τ pr.1).comp
          (quarticLegOperatorForSequence ε q τ pr.2))) :=
  continuous_const.mul (continuous_finsetProd _ fun pr _ =>
    continuous_coordinate_expectation_quarticLegOperatorForSequence_pair ε β q pr.1 pr.2)

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

/-- **The ordered-simplex integral of `freeGibbsExpectation ∘ nestedVertexOperatorComp`, as a sum
over pairings of integrated contraction terms** — rewrites the integrand pointwise via
`coordinate_expectation_nestedVertexOperatorComp_eq_sum_pairing`
(`intervalIntegral.orderedSimplexIntegral_congr`), pulls the finite `Pairing (2 * n)` sum out past
the integral (`intervalIntegral.orderedSimplexIntegral_finsetSum`, using
`continuous_coordinate_flatVertexLegPairingTerm` for its integrability side condition), then pulls each
pairing's `τ`-independent weight back out of its own integral
(`intervalIntegral.orderedSimplexIntegral_smul`). -/
private theorem coordinate_orderedSimplexIntegral_nestedVertexOperatorComp_eq_sum_pairing
    (ε : Mode → ℝ) (β t : ℝ) (n : ℕ) (q : Fin n → QuarticVertexLabel Mode) :
    intervalIntegral.orderedSimplexIntegral n t
        (fun τ => freeGibbsExpectation ε β (nestedVertexOperatorComp ε n q τ)) =
      ∑ pairing : Combinatorics.Pairing (2 * n),
        pairing.weight Common.Statistics.fermion *
          intervalIntegral.orderedSimplexIntegral n t
            (fun τ => ∏ pr ∈ pairing.pairs, freeGibbsExpectation ε β
              ((quarticLegOperatorForSequence ε q τ pr.1).comp
                (quarticLegOperatorForSequence ε q τ pr.2))) := by
  rw [intervalIntegral.orderedSimplexIntegral_congr
      (fun τ => coordinate_expectation_nestedVertexOperatorComp_eq_sum_pairing ε β n q τ),
    intervalIntegral.orderedSimplexIntegral_finsetSum _ n t _
      (fun pairing _ => continuous_coordinate_flatVertexLegPairingTerm ε β q pairing)]
  exact Finset.sum_congr rfl fun pairing _ => intervalIntegral.orderedSimplexIntegral_smul n t _ _

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
  simpa only [freeGibbsDensityOperator_expectation_eq_freeGibbsExpectation] using
    coordinate_orderedSimplexIntegral_nestedVertexOperatorComp_eq_sum_pairing ε β t n q

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
