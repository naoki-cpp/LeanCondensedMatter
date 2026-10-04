import LeanCondensedMatter.Analysis.OrderedSimplex.FamilyShuffle
import LeanCondensedMatter.Combinatorics.FinpartitionOrderShuffle
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Ordered
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Factorization.ComponentVertexProduct
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.Wick.ComponentContractionIntegrand
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.Wick.Amplitude

set_option linter.style.header false

/-!
# Component factorization of quartic Wick-diagram amplitudes

The global vertex-order sum is reindexed by component-local orders and component shuffles. For each
fixed family of local orders, contraction-integrand factorization identifies the global integrand
with the generic family-shuffle integrand, so the ordered-simplex product theorem applies directly.
The remaining finite sum over families of component orders distributes into the product of the local
order sums. Combining this with the Common scalar-prefactor factorization gives the quartic
Wick-amplitude factorization.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {N : ℕ}

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
  let localContribution :
      ∀ B : d.vertexGraph.componentPartitionOn.parts,
        Common.QuarticVertexOrder (B : Finset (Fin N)) → ℂ :=
    fun B order => QuarticWickDiagram.orderedSimplexContribution ε β
      (d.restrictComponentConnected B.2).1 order
  simpa only [one_mul] using
    (Finpartition.sum_order_eq_mul_prod_sum_partOrders
      d.vertexGraph.componentPartitionOn
      (fun order : Common.QuarticVertexOrder S =>
        d.orderedSimplexContribution ε β order)
      localContribution (1 : ℂ) (fun orders => by
        simp only [one_mul, QuarticWickDiagram.orderedSimplexContribution]
        let componentIntegrand :
            ∀ B : d.vertexGraph.componentPartitionOn.parts,
              (Fin (B : Finset (Fin N)).card → ℝ) → ℂ :=
          fun B => QuarticWickDiagram.contractionIntegrand ε β
            (d.restrictComponentConnected B.2).1 (orders B)
        have hglobal (shuffle : d.ComponentShuffle) :
            d.contractionIntegrand ε β (d.assembleVertexOrder orders shuffle) =
              shuffle.ambientIntegrand componentIntegrand := by
          funext τ
          exact d.contractionIntegrand_assembleVertexOrder_eq_prod_components
            ε β orders shuffle τ
        simp_rw [hglobal]
        have hcard :
            (∑ B : d.vertexGraph.componentPartitionOn.parts,
              (B : Finset (Fin N)).card) = S.card := by
          rw [Finset.sum_coe_sort]
          exact d.vertexGraph.componentPartitionOn.sum_card_parts
        simpa only [localContribution, QuarticWickDiagram.orderedSimplexContribution,
          componentIntegrand] using
          Combinatorics.FamilySlotShuffleTo.sum_integral_eq_prod
            (ι := d.vertexGraph.componentPartitionOn.parts)
            (fun B : d.vertexGraph.componentPartitionOn.parts =>
              (B : Finset (Fin N)).card)
            S.card hcard β componentIntegrand
            (fun B => intervalIntegral.Continuous.measurableLocallyBounded
              (continuous_contractionIntegrand ε β
                (d.restrictComponentConnected B.2).1 (orders B)))))


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

end Fermionic
end SecondQuantization
