import LeanCondensedMatter.Analysis.OrderedSimplex.FamilyShuffleIntegrand
import LeanCondensedMatter.Analysis.OrderedSimplex.PartitionOrderIntegral
import LeanCondensedMatter.Combinatorics.Cumulant.ConnectedDecomposition
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Components.ComponentConnected
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Components.ComponentDecompositionEquiv
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Ordered
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Factorization.ComponentEvaluation
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Factorization.ComponentVertexProduct
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Pairing.ComponentPairing
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.Wick.Amplitude

set_option linter.style.header false

/-!
# Component factorization of quartic Wick-diagram amplitudes

The statistics-independent component embeddings and pairing-evaluation factorization live in
`SecondQuantization.Common`. This module proves compatibility of fermionic operators and pair
values with those embeddings, then factors the fixed-order contraction integrand over connected
components. Reindexing the global vertex orders by component-local orders and shuffles allows
ordered-simplex factorization and yields the multiplicative Wick-diagram amplitude.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} {N : ℕ}

section ComponentPairValue

variable [LinearOrder Mode]

/-- A global ordered leg at a component-embedded position equals the corresponding ordered leg of
its restricted component diagram. -/
private theorem orderedQuarticLegOperator_componentOrderedLeg
    (ε : Mode → ℝ) {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (τ : Fin S.card → ℝ) (B : d.vertexGraph.componentPartitionOn.parts)
    (p : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    orderedQuarticLegOperator ε d (d.assembleVertexOrder orders shuffle) τ
        (d.componentOrderedLeg shuffle B p) =
      orderedQuarticLegOperator ε (d.restrictComponent B.2) (orders B)
        (shuffle.timeAssignment τ B) p := by
  unfold orderedQuarticLegOperator quarticLegOperatorForSequence
  simp only [d.orderedQuarticLegEquiv_componentOrderedLeg,
    Combinatorics.FamilySlotShuffleTo.timeAssignment_apply]
  rw [d.restrictComponent_vertexLabel_componentOrder orders shuffle B]

variable [Fintype Mode]

/-- Pair values agree after embedding both component-local ordered legs into the assembled global
ordered-leg enumeration. -/
theorem orderedQuarticPairValue_componentOrderedLeg (ε : Mode → ℝ) (β : ℝ)
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (τ : Fin S.card → ℝ) (B : d.vertexGraph.componentPartitionOn.parts)
    (a b : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    orderedQuarticPairValue ε β d (d.assembleVertexOrder orders shuffle) τ
        (d.componentOrderedLeg shuffle B a) (d.componentOrderedLeg shuffle B b) =
      orderedQuarticPairValue ε β (d.restrictComponent B.2) (orders B)
        (shuffle.timeAssignment τ B) a b := by
  rw [orderedQuarticPairValue_eq_finiteGibbsExpectation,
    orderedQuarticPairValue_eq_finiteGibbsExpectation,
    orderedQuarticLegOperator_componentOrderedLeg,
    orderedQuarticLegOperator_componentOrderedLeg]

end ComponentPairValue

variable [LinearOrder Mode] [Fintype Mode]

/-! ## Component contraction integrand -/

/-- The Wick contraction integrand of an assembled vertex order is the product of the contraction
integrands of its connected components, evaluated on the corresponding restricted time
assignments. -/
theorem QuarticWickDiagram.contractionIntegrand_assembleVertexOrder_eq_prod_components
    (ε : Mode → ℝ) (β : ℝ) {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (τ : Fin S.card → ℝ) :
    d.contractionIntegrand ε β (d.assembleVertexOrder orders shuffle) τ =
      ∏ B : d.vertexGraph.componentPartitionOn.parts,
        QuarticWickDiagram.contractionIntegrand ε β
          (d.restrictComponentConnected B.2).1 (orders B)
          (shuffle.timeAssignment τ B) := by
  classical
  simpa only [QuarticWickDiagram.contractionIntegrand,
    Common.QuarticDiagram.restrictComponentConnected] using
    d.pairingInOrder_evaluation_eq_prod_components Common.Statistics.fermion orders shuffle
      (orderedQuarticPairValue ε β d (d.assembleVertexOrder orders shuffle) τ)
      (fun B => orderedQuarticPairValue ε β (d.restrictComponent B.2) (orders B)
        (shuffle.timeAssignment τ B))
      (fun B a b => orderedQuarticPairValue_componentOrderedLeg
        ε β d orders shuffle τ B a b)

/-! ## Wick amplitude factorization -/

/-- The sum of ordered-simplex contributions over all global vertex orders factors as the product of
the corresponding sums for the connected-component restrictions. -/
private theorem sum_orderedSimplexContribution_eq_prod_components
    (ε : Mode → ℝ) (β : ℝ) {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) :
    (∑ order : Common.QuarticVertexOrder S, d.orderedSimplexContribution ε β order) =
      ∏ B : d.vertexGraph.componentPartitionOn.parts,
        ∑ order : Common.QuarticVertexOrder (B : Finset (Fin N)),
          QuarticWickDiagram.orderedSimplexContribution ε β
            (d.restrictComponentConnected B.2).1 order := by
  classical
  simpa only [QuarticWickDiagram.orderedSimplexContribution] using
    (Finpartition.sum_order_orderedSimplexIntegral_eq_prod_sum_partOrders
      d.vertexGraph.componentPartitionOn β
      (fun order => d.contractionIntegrand ε β order)
      (fun B order => QuarticWickDiagram.contractionIntegrand ε β
        (d.restrictComponentConnected B.2).1 order)
      (fun orders shuffle => by
        funext τ
        exact d.contractionIntegrand_assembleVertexOrder_eq_prod_components
          ε β orders shuffle τ)
      (fun B order => intervalIntegral.Continuous.measurableLocallyBounded
        (continuous_contractionIntegrand ε β (d.restrictComponentConnected B.2).1 order)))

/-- A quartic Wick-diagram amplitude is the product of the amplitudes of its connected components. -/
theorem quarticWickDiagramAmplitude_eq_prod_components
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) :
    quarticWickDiagramAmplitude ε β g d =
      ∏ B : d.vertexGraph.componentPartitionOn.parts,
        quarticWickDiagramAmplitude ε β g (d.restrictComponentConnected B.2).1 := by
  classical
  simp only [quarticWickDiagramAmplitude]
  rw [Common.QuarticDiagram.dysonSign_mul_vertexWeight_eq_prod_components d g,
    sum_orderedSimplexContribution_eq_prod_components ε β d]
  rw [← Finset.prod_mul_distrib]

/-! ## Multiplicative weight for connected components -/

/-- The fermionic quartic Wick amplitude as a multiplicative weight on the shared connected
quartic-diagram decomposition. -/
noncomputable def quarticWickDiagramMultiplicativeWeight
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) :
    Combinatorics.MultiplicativeWeight
      (Common.quarticDiagramConnectedDecomposition (QuarticVertexLabel Mode) N) ℂ :=
  Common.QuarticDiagram.multiplicativeWeight
    (N := N)
    (fun d => quarticWickDiagramAmplitude ε β g d)
    (fun d => quarticWickDiagramAmplitude_eq_prod_components ε β g d)

end Fermionic
end SecondQuantization
