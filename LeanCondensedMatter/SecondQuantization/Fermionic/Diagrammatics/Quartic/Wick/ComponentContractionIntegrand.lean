import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Components.ComponentConnected
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Factorization.ComponentEvaluation
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.Wick.ComponentPairValue

set_option linter.style.header false

/-!
# Component factorization of the fermionic contraction integrand

Common owns the Statistics-generic pairing-evaluation factorization. This module supplies only the
fermionic Gibbs pair kernel and its locality under the Common component leg embedding, yielding the
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
  simpa only [QuarticWickDiagram.contractionIntegrand,
    Common.QuarticDiagram.restrictComponentConnected] using
    d.pairingInOrder_evaluation_eq_prod_components Common.Statistics.fermion orders shuffle
      (orderedQuarticPairValue ε β d (d.assembleVertexOrder orders shuffle) τ)
      (fun B => orderedQuarticPairValue ε β (d.restrictComponent B.2) (orders B)
        (d.componentTimeAssignment shuffle τ B))
      (fun B a b => orderedQuarticPairValue_componentOrderedLeg
        ε β d orders shuffle τ B a b)

end Fermionic
end SecondQuantization
