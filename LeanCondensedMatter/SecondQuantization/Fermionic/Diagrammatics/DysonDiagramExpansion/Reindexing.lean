import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion.Pairing
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.Amplitude

set_option linter.style.header false

/-!
# Dyson diagram expansion: diagram reindexing
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-! ## Reindexing into a sum over `QuarticWickDiagram`s -/

omit [Fintype Mode] [LinearOrder Mode] in
/-- **A diagram's coupling weight, reindexed along a vertex order** — `Equiv.prod_comp` at `order`
turns the product over the vertex set `↥S` into a product over time slots `Fin S.card`. -/
theorem couplingWeight_eq_prod_vertexLabel_order {N : ℕ} {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (g : QuarticVertexLabel Mode → ℂ)
    (order : Common.QuarticVertexOrder S) :
    d.couplingWeight g = ∏ i : Fin S.card, g (d.vertexLabel (order i)) := by
  rw [QuarticWickDiagram.couplingWeight]
  exact (Equiv.prod_comp order (fun v => g (d.vertexLabel v))).symm

/-- **A diagram's fixed-order ordered-simplex contribution, expressed through canonical
free Gibbs density-state contractions of its flattened leg pairs.** -/
theorem orderedSimplexContribution_eq_pairing_sum_term {N : ℕ} {S : Finset (Fin N)} (ε : Mode → ℝ)
    (β : ℝ) (d : QuarticWickDiagram Mode N S) (order : Common.QuarticVertexOrder S) :
    d.orderedSimplexContribution ε β order =
      (d.pairingInOrder order).weight Common.Statistics.fermion *
        intervalIntegral.orderedSimplexIntegral S.card β
          (fun τ => ∏ pr ∈ (d.pairingInOrder order).pairs,
            (freeGibbsDensityOperator ε β).expectation
              (Common.finiteHilbertOperator
                ((quarticLegOperatorForSequence ε (fun i => d.vertexLabel (order i)) τ pr.1).comp
                  (quarticLegOperatorForSequence ε (fun i => d.vertexLabel (order i)) τ pr.2)))) := by
  rw [QuarticWickDiagram.orderedSimplexContribution]
  have heq : d.contractionIntegrand ε β order = fun τ =>
      (d.pairingInOrder order).weight Common.Statistics.fermion *
        ∏ pr ∈ (d.pairingInOrder order).pairs,
          (freeGibbsDensityOperator ε β).expectation
            (Common.finiteHilbertOperator
              ((quarticLegOperatorForSequence ε (fun i => d.vertexLabel (order i)) τ pr.1).comp
                (quarticLegOperatorForSequence ε (fun i => d.vertexLabel (order i)) τ pr.2))) := by
    funext τ
    rw [QuarticWickDiagram.contractionIntegrand]
    refine congrArg (_ * ·) (Finset.prod_congr rfl fun pr _ => ?_)
    rw [orderedQuarticPairValue_eq_freeGibbsDensityOperator_expectation,
      orderedQuarticLegOperator]
  rw [heq, intervalIntegral.orderedSimplexIntegral_smul]

/-- **A diagram's coupling weight times its fixed-order ordered-simplex contribution**,
entirely in terms of the vertex-label sequence, transported pairing, and canonical density-state
pair values. -/
theorem couplingWeight_mul_orderedSimplexContribution_eq {N : ℕ} {S : Finset (Fin N)}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) (d : QuarticWickDiagram Mode N S)
    (order : Common.QuarticVertexOrder S) :
    d.couplingWeight g * d.orderedSimplexContribution ε β order =
      (∏ i : Fin S.card, g (d.vertexLabel (order i))) *
        ((d.pairingInOrder order).weight Common.Statistics.fermion *
          intervalIntegral.orderedSimplexIntegral S.card β
            (fun τ => ∏ pr ∈ (d.pairingInOrder order).pairs,
              (freeGibbsDensityOperator ε β).expectation
                (Common.finiteHilbertOperator
                  ((quarticLegOperatorForSequence ε (fun i => d.vertexLabel (order i)) τ pr.1).comp
                    (quarticLegOperatorForSequence ε (fun i => d.vertexLabel (order i)) τ pr.2))))) := by
  rw [couplingWeight_eq_prod_vertexLabel_order, orderedSimplexContribution_eq_pairing_sum_term]

/-- **Summing `couplingWeight * orderedSimplexContribution` over all diagrams at a fixed
vertex order gives the vertex-label/pairing double sum with canonical density-state
contractions.** -/
theorem sum_couplingWeight_mul_orderedSimplexContribution_eq {N : ℕ} {S : Finset (Fin N)}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (order : Common.QuarticVertexOrder S) :
    ∑ d : QuarticWickDiagram Mode N S,
        d.couplingWeight g * d.orderedSimplexContribution ε β order =
      ∑ q : Fin S.card → QuarticVertexLabel Mode, (∏ i, g (q i)) *
        ∑ pairing : Combinatorics.Pairing (2 * S.card),
          pairing.weight Common.Statistics.fermion *
            intervalIntegral.orderedSimplexIntegral S.card β
              (fun τ => ∏ pr ∈ pairing.pairs,
                (freeGibbsDensityOperator ε β).expectation
                  (Common.finiteHilbertOperator
                    ((quarticLegOperatorForSequence ε q τ pr.1).comp
                      (quarticLegOperatorForSequence ε q τ pr.2)))) :=
  calc
    ∑ d : QuarticWickDiagram Mode N S,
        d.couplingWeight g * d.orderedSimplexContribution ε β order =
      ∑ d : QuarticWickDiagram Mode N S,
        (fun x : Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) S.card =>
          (∏ i, g (x.1 i)) * (x.2.weight Common.Statistics.fermion *
            intervalIntegral.orderedSimplexIntegral S.card β
              (fun τ => ∏ pr ∈ x.2.pairs,
                (freeGibbsDensityOperator ε β).expectation
                  (Common.finiteHilbertOperator
                    ((quarticLegOperatorForSequence ε x.1 τ pr.1).comp
                      (quarticLegOperatorForSequence ε x.1 τ pr.2))))))
          (Common.quarticDiagramEquivOrderedData order d) :=
        Finset.sum_congr rfl fun d _ => by
          simp only [Common.quarticDiagramEquivOrderedData]
          exact couplingWeight_mul_orderedSimplexContribution_eq ε β g d order
    _ = ∑ x : Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) S.card,
        (∏ i, g (x.1 i)) * (x.2.weight Common.Statistics.fermion *
          intervalIntegral.orderedSimplexIntegral S.card β
            (fun τ => ∏ pr ∈ x.2.pairs,
              (freeGibbsDensityOperator ε β).expectation
                (Common.finiteHilbertOperator
                  ((quarticLegOperatorForSequence ε x.1 τ pr.1).comp
                    (quarticLegOperatorForSequence ε x.1 τ pr.2))))) :=
        Common.sum_quarticDiagram_eq_sum_orderedData order
          (fun x : Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) S.card =>
            (∏ i, g (x.1 i)) * (x.2.weight Common.Statistics.fermion *
              intervalIntegral.orderedSimplexIntegral S.card β
                (fun τ => ∏ pr ∈ x.2.pairs,
                  (freeGibbsDensityOperator ε β).expectation
                    (Common.finiteHilbertOperator
                      ((quarticLegOperatorForSequence ε x.1 τ pr.1).comp
                        (quarticLegOperatorForSequence ε x.1 τ pr.2))))))
    _ = ∑ q : Fin S.card → QuarticVertexLabel Mode,
        ∑ pairing : Combinatorics.Pairing (2 * S.card),
          (∏ i, g (q i)) * (pairing.weight Common.Statistics.fermion *
            intervalIntegral.orderedSimplexIntegral S.card β
              (fun τ => ∏ pr ∈ pairing.pairs,
                (freeGibbsDensityOperator ε β).expectation
                  (Common.finiteHilbertOperator
                    ((quarticLegOperatorForSequence ε q τ pr.1).comp
                      (quarticLegOperatorForSequence ε q τ pr.2))))) :=
        Fintype.sum_prod_type _
    _ = ∑ q : Fin S.card → QuarticVertexLabel Mode, (∏ i, g (q i)) *
        ∑ pairing : Combinatorics.Pairing (2 * S.card),
          pairing.weight Common.Statistics.fermion *
            intervalIntegral.orderedSimplexIntegral S.card β
              (fun τ => ∏ pr ∈ pairing.pairs,
                (freeGibbsDensityOperator ε β).expectation
                  (Common.finiteHilbertOperator
                    ((quarticLegOperatorForSequence ε q τ pr.1).comp
                      (quarticLegOperatorForSequence ε q τ pr.2)))) :=
        Finset.sum_congr rfl fun q _ => (Finset.mul_sum _ _ _).symm

/-- **PR 6's final theorem: `dysonVertexMoment` of `quarticInteraction` is the sum, over every
`QuarticWickDiagram`, of `quarticWickDiagramAmplitude`.** Swaps the diagram sum's `∑ order`
(from `quarticWickDiagramAmplitude`'s own definition) to the outside, applies
`sum_couplingWeight_mul_orderedSimplexContribution_eq` at each fixed order to get an
order-independent vertex-label/pairing double sum, then collapses the resulting `∑ order` of a
constant via `Common.card_quarticVertexOrder` (`Fintype.card (Common.QuarticVertexOrder S) = S.card!`) to match
`dysonVertexMoment_quarticInteraction_eq_sum_vertexLabel_pairing`'s own `S.card!` prefactor. -/
theorem sum_quarticWickDiagramAmplitude_eq_dysonVertexMoment (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) {N : ℕ} (S : Finset (Fin N)) :
    ∑ d : QuarticWickDiagram Mode N S, quarticWickDiagramAmplitude ε β g d =
      dysonVertexMoment ε β (quarticInteraction g) S := by
  rw [dysonVertexMoment_quarticInteraction_eq_sum_vertexLabel_pairing]
  have hstep : ∑ d : QuarticWickDiagram Mode N S, quarticWickDiagramAmplitude ε β g d =
      (-1 : ℂ) ^ S.card * ∑ order : Common.QuarticVertexOrder S,
        ∑ q : Fin S.card → QuarticVertexLabel Mode, (∏ i, g (q i)) *
          ∑ pairing : Combinatorics.Pairing (2 * S.card),
            pairing.weight Common.Statistics.fermion *
              intervalIntegral.orderedSimplexIntegral S.card β
                (fun τ => ∏ pr ∈ pairing.pairs,
                  (freeGibbsDensityOperator ε β).expectation
                    (Common.finiteHilbertOperator
                      ((quarticLegOperatorForSequence ε q τ pr.1).comp
                        (quarticLegOperatorForSequence ε q τ pr.2)))) := by
    have hpt : ∀ d : QuarticWickDiagram Mode N S, quarticWickDiagramAmplitude ε β g d =
        (-1 : ℂ) ^ S.card *
          ∑ order : Common.QuarticVertexOrder S,
            d.couplingWeight g * d.orderedSimplexContribution ε β order :=
      fun d => by rw [quarticWickDiagramAmplitude, mul_assoc, Finset.mul_sum]
    calc
      ∑ d : QuarticWickDiagram Mode N S, quarticWickDiagramAmplitude ε β g d
          = ∑ d : QuarticWickDiagram Mode N S, (-1 : ℂ) ^ S.card *
              ∑ order : Common.QuarticVertexOrder S,
                d.couplingWeight g * d.orderedSimplexContribution ε β order :=
          Finset.sum_congr rfl fun d _ => hpt d
      _ = (-1 : ℂ) ^ S.card * ∑ d : QuarticWickDiagram Mode N S,
            ∑ order : Common.QuarticVertexOrder S,
              d.couplingWeight g * d.orderedSimplexContribution ε β order :=
          (Finset.mul_sum _ _ _).symm
      _ = (-1 : ℂ) ^ S.card * ∑ order : Common.QuarticVertexOrder S,
            ∑ d : QuarticWickDiagram Mode N S,
              d.couplingWeight g * d.orderedSimplexContribution ε β order := by
          rw [Finset.sum_comm]
      _ = (-1 : ℂ) ^ S.card * ∑ order : Common.QuarticVertexOrder S,
            ∑ q : Fin S.card → QuarticVertexLabel Mode, (∏ i, g (q i)) *
              ∑ pairing : Combinatorics.Pairing (2 * S.card),
                pairing.weight Common.Statistics.fermion *
                  intervalIntegral.orderedSimplexIntegral S.card β
                    (fun τ => ∏ pr ∈ pairing.pairs,
                      (freeGibbsDensityOperator ε β).expectation
                        (Common.finiteHilbertOperator
                          ((quarticLegOperatorForSequence ε q τ pr.1).comp
                            (quarticLegOperatorForSequence ε q τ pr.2)))) := by
          congr 1
          exact Finset.sum_congr rfl fun order _ =>
            sum_couplingWeight_mul_orderedSimplexContribution_eq ε β g order
  rw [hstep, Finset.sum_const, Finset.card_univ, Common.card_quarticVertexOrder]
  ring

/-- **PR 6, complete**: `dysonVertexMoment ε β (quarticInteraction g) S` is the sum, over every
`QuarticWickDiagram Mode N S`, of `quarticWickDiagramAmplitude ε β g d` — the canonical direction
of `sum_quarticWickDiagramAmplitude_eq_dysonVertexMoment`, matching the statement this whole line
of PRs (Step 6 PR 6, `notes/roadmaps/second-quantization.md`) has been building towards. -/
theorem dysonVertexMoment_quarticInteraction_eq_sum_quarticWickDiagramAmplitude (ε : Mode → ℝ)
    (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) {N : ℕ} (S : Finset (Fin N)) :
    dysonVertexMoment ε β (quarticInteraction g) S =
      ∑ d : QuarticWickDiagram Mode N S, quarticWickDiagramAmplitude ε β g d :=
  (sum_quarticWickDiagramAmplitude_eq_dysonVertexMoment ε β g S).symm


end Fermionic
end SecondQuantization
