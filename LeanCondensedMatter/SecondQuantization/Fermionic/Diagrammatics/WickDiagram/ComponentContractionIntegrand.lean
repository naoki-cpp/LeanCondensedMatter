import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.ComponentConnected
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentPairProduct
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.ComponentGlobalCrossingParity

set_option linter.style.header false

/-!
# Component factorization of the fermionic contraction integrand

The product of ordered pair values and the Statistics-generic pairing weight both factor over
connected components for every assembled component shuffle. Combining those two results gives the
fixed-order contraction-integrand factorization required by milestone M1 of the fermionic
linked-cluster theorem.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {N : ℕ}

/-- The Wick contraction integrand of an assembled vertex order is the product of the contraction
integrands of its connected components, evaluated on the corresponding restricted time
assignments. -/
theorem QuarticWickDiagram.contractionIntegrand_assembleVertexOrder_eq_prod_components
    (ε : Mode → ℝ) (β : ℝ) {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (τ : Fin S.card → ℝ) :
    d.contractionIntegrand ε β (d.assembleVertexOrder orders shuffle) τ =
      ∏ B : d.componentPartition.parts,
        QuarticWickDiagram.contractionIntegrand ε β
          (d.restrictComponentConnected B.2).1 (orders B)
          (d.componentTimeAssignment shuffle τ B) := by
  classical
  simp only [QuarticWickDiagram.contractionIntegrand, Combinatorics.Pairing.evaluation]
  rw [d.pairingInOrder_weight_eq_prod_components Common.Statistics.fermion orders shuffle,
    d.prod_orderedQuarticPairValue_pairs_eq_prod_components ε β orders shuffle τ,
    ← Finset.prod_mul_distrib]
  simp only [Common.QuarticDiagram.restrictComponentConnected]

end Fermionic
end SecondQuantization
