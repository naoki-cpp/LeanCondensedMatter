import LeanCondensedMatter.Analysis.OrderedSimplex.FamilyOrderShuffleFintype
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
      ∏ B : d.componentPartition.parts,
        ∑ order : Common.QuarticVertexOrder (B : Finset (Fin N)),
          QuarticWickDiagram.orderedSimplexContribution ε β
            (d.restrictComponentConnected B.2).1 order := by
  classical
  let F := fun B : d.componentPartition.parts => ↥(B : Finset (Fin N))
  have hcard : (∑ B : d.componentPartition.parts, Fintype.card (F B)) = S.card := by
    simp only [F, Fintype.card_coe]
    rw [Finset.sum_coe_sort]
    exact d.componentPartition.sum_card_parts
  have hfactor :
      ∀ (orders : Combinatorics.FamilyOrders F)
        (shuffle : Combinatorics.FamilySlotShuffleTo
          (fun B => Fintype.card (F B)) S.card),
        d.contractionIntegrand ε β
            (Combinatorics.assembleFamilyOrder F
              d.componentPartition.equivSigmaParts orders shuffle) =
          shuffle.ambientIntegrand
            (fun B => QuarticWickDiagram.contractionIntegrand ε β
              (d.restrictComponentConnected B.2).1 (orders B)) := by
    intro orders shuffle
    funext τ
    exact d.contractionIntegrand_assembleVertexOrder_eq_prod_components
      ε β orders shuffle τ
  simpa only [QuarticWickDiagram.orderedSimplexContribution, F, Fintype.card_coe] using
    Combinatorics.sum_orderedSimplexIntegral_eq_prod_localOrderSums
      F S.card hcard d.componentPartition.equivSigmaParts β
      (fun order => d.contractionIntegrand ε β order)
      (fun B order =>
        QuarticWickDiagram.contractionIntegrand ε β
          (d.restrictComponentConnected B.2).1 order)
      hfactor
      (fun B order =>
        continuous_contractionIntegrand ε β
          (d.restrictComponentConnected B.2).1 order)

/-- A quartic Wick-diagram amplitude is the product of the amplitudes of its connected components. -/
theorem quarticWickDiagramAmplitude_eq_prod_components
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) :
    quarticWickDiagramAmplitude ε β g d =
      ∏ B : d.componentPartition.parts,
        quarticWickDiagramAmplitude ε β g (d.restrictComponentConnected B.2).1 := by
  classical
  simp only [quarticWickDiagramAmplitude]
  rw [Common.QuarticDiagram.dysonSign_mul_vertexWeight_eq_prod_components d g,
    sum_orderedSimplexContribution_eq_prod_components ε β d]
  rw [← Finset.prod_mul_distrib]

end Fermionic
end SecondQuantization
