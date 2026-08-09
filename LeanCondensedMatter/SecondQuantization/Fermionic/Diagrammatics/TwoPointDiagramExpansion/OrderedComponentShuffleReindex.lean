import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentOrderRelabel
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.OrderedComponentShuffleBridge
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.IntegratedComponentFactorization
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.OrderedRelabel

set_option linter.style.header false

/-!
# Reindexing ordered two-point component shuffles

For fixed component-local interaction orders, changing only the component shuffle changes the
explicit ordered presentation by exactly the component-shuffle interaction relabeling.  This is the
finite combinatorial bridge between the arbitrary-set global-order sum and the integrated shuffle
factorization.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {N : ℕ}

/-- With component-local orders fixed, the ordered presentation for an arbitrary component shuffle
is the canonical-shuffle presentation relabeled by the corresponding explicit component shuffle. -/
theorem fixedExternalTwoPointWickDiagramOrderEquiv_assemble_eq_relabelForComponentShuffle
    {S : Finset (Fin N)} (i j : Mode)
    (d : FixedExternalTwoPointWickDiagramOn Mode N S i j)
    (orders : d.1.ComponentInteractionVertexOrders)
    (shuffle : d.1.ComponentInteractionShuffle) :
    let baseOrder := d.1.assembleInteractionVertexOrder orders
      d.1.canonicalComponentInteractionShuffle
    let base := fixedExternalTwoPointWickDiagramOrderEquiv i j baseOrder d
    let explicitShuffle :=
      (d.1.inInteractionOrderComponentShuffleEquiv baseOrder).symm shuffle
    base.relabelForComponentShuffle explicitShuffle =
      fixedExternalTwoPointWickDiagramOrderEquiv i j
        (d.1.assembleInteractionVertexOrder orders shuffle) d := by
  dsimp only
  rw [← fixedExternalTwoPointWickDiagramOrderEquiv_relabel_orderChange
    i j d
    (d.1.assembleInteractionVertexOrder orders d.1.canonicalComponentInteractionShuffle)
    (d.1.assembleInteractionVertexOrder orders shuffle)]
  unfold FixedExternalTwoPointWickDiagram.relabelForComponentShuffle
  congr 1
  rw [d.1.assembleInteractionVertexOrder_change orders shuffle
    d.1.canonicalComponentInteractionShuffle]
  apply Equiv.ext
  intro v
  simp [FixedExternalTwoPointWickDiagram.componentShuffleSlotPermutation,
    Common.TwoPointDiagram.ComponentInteractionShuffle.ambientPermutation,
    Common.TwoPointDiagram.inInteractionOrderComponentShuffleEquiv,
    Common.familySlotShuffleCastSizeEquiv,
    Common.TwoPointDiagram.componentInteractionFamilyShuffleEquiv,
    Combinatorics.FamilySlotShuffle.reindexEquiv,
    Combinatorics.FamilySlotShuffleTo.castTotalEquiv,
    Common.TwoPointDiagram.inInteractionOrderComponentShuffleEquiv_canonical]

end Fermionic
end SecondQuantization
