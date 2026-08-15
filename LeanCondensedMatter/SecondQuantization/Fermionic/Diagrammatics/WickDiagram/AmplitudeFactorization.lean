import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Ordered
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.ComponentOrderedSimplex
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.ComponentVertexProduct
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentContractionIntegrand
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.Amplitude

set_option linter.style.header false

/-!
# Component factorization of quartic Wick-diagram amplitudes

The global vertex-order sum is reindexed by component-local orders and component shuffles. For each
fixed family of local orders, the M1 contraction-integrand factorization identifies the global
integrand with the component-shuffle integrand, so the M0 ordered-simplex product theorem applies.
The remaining finite sum over families of component orders distributes into the product of the local
order sums. Combining this with the Common scalar-prefactor factorization gives the full M2 quartic
Wick-amplitude factorization. No new diagram combinatorics or amplitude convention is introduced at
this assembly boundary.
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
  let localContribution :
      ∀ B : d.componentPartition.parts,
        Common.QuarticVertexOrder (B : Finset (Fin N)) → ℂ :=
    fun B order => QuarticWickDiagram.orderedSimplexContribution ε β
      (d.restrictComponentConnected B.2).1 order
  calc
    (∑ order : Common.QuarticVertexOrder S, d.orderedSimplexContribution ε β order) =
        ∑ x : d.ComponentVertexOrders × d.ComponentShuffle,
          d.orderedSimplexContribution ε β (d.assembleVertexOrder x.1 x.2) := by
      rw [← Equiv.sum_comp (Common.QuarticDiagram.componentOrderDecompositionEquiv d).symm]
      rfl
    _ = ∑ orders : d.ComponentVertexOrders,
          ∑ shuffle : d.ComponentShuffle,
            d.orderedSimplexContribution ε β
              (d.assembleVertexOrder orders shuffle) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ orders : d.ComponentVertexOrders,
          ∏ B : d.componentPartition.parts, localContribution B (orders B) := by
      apply Fintype.sum_congr
      intro orders
      simp only [QuarticWickDiagram.orderedSimplexContribution]
      let componentIntegrand :
          ∀ B : d.componentPartition.parts,
            (Fin (B : Finset (Fin N)).card → ℝ) → ℂ :=
        fun B => QuarticWickDiagram.contractionIntegrand ε β
          (d.restrictComponentConnected B.2).1 (orders B)
      have hglobal (shuffle : d.ComponentShuffle) :
          d.contractionIntegrand ε β (d.assembleVertexOrder orders shuffle) =
            d.componentShuffleIntegrand shuffle componentIntegrand := by
        funext τ
        exact d.contractionIntegrand_assembleVertexOrder_eq_prod_components
          ε β orders shuffle τ
      simp_rw [hglobal]
      simpa only [localContribution, QuarticWickDiagram.orderedSimplexContribution,
        componentIntegrand] using
        d.sum_componentShuffle_orderedSimplexIntegral_eq_prod β componentIntegrand
          (fun B => continuous_contractionIntegrand ε β
            (d.restrictComponentConnected B.2).1 (orders B))
    _ = ∏ B : d.componentPartition.parts,
          ∑ order : Common.QuarticVertexOrder (B : Finset (Fin N)),
            localContribution B order := by
      simpa using
        (Finset.prod_univ_sum
          (fun B : d.componentPartition.parts =>
            (Finset.univ : Finset (Common.QuarticVertexOrder (B : Finset (Fin N)))))
          localContribution).symm
    _ = ∏ B : d.componentPartition.parts,
          ∑ order : Common.QuarticVertexOrder (B : Finset (Fin N)),
            QuarticWickDiagram.orderedSimplexContribution ε β
              (d.restrictComponentConnected B.2).1 order := by
      rfl

/-- A quartic Wick-diagram amplitude is the product of the amplitudes of its connected-component
restrictions. This is the exit theorem of milestone M2 of the fermionic linked-cluster roadmap. -/
theorem quarticWickDiagramAmplitude_eq_prod_restrictComponentConnected
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) :
    quarticWickDiagramAmplitude ε β g d =
      ∏ B : d.componentPartition.parts,
        quarticWickDiagramAmplitude ε β g (d.restrictComponentConnected B.2).1 := by
  classical
  simp only [quarticWickDiagramAmplitude, QuarticWickDiagram.couplingWeight]
  rw [Common.QuarticDiagram.dysonSign_mul_vertexWeight_eq_prod_restrictComponentConnected d g,
    sum_orderedSimplexContribution_eq_prod_components ε β d]
  rw [← Finset.prod_mul_distrib]

end Fermionic
end SecondQuantization
