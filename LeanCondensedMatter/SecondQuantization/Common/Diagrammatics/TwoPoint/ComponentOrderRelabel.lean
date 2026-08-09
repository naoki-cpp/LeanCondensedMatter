import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentOrderDecomposition

set_option linter.style.header false

/-!
# Relabeling between assembled component orders

Once the component-local vertex orders are fixed, changing only the component interleaving changes
the resulting global interaction order by exactly the ambient slot permutation between those two
shuffles.  This is the finite-order identity needed by the external-leg LCT reindexing step.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

noncomputable section

/-- The slot permutation taking one assembled component order to another is just the corresponding
change of component shuffle; the local vertex-order equivalence cancels. -/
theorem TwoPointDiagram.assembleInteractionVertexOrder_change
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (orders : d.ComponentInteractionVertexOrders)
    (base target : d.ComponentInteractionShuffle) :
    (d.assembleInteractionVertexOrder orders target).trans
        (d.assembleInteractionVertexOrder orders base).symm =
      target.slotEquiv.symm.trans base.slotEquiv := by
  ext i
  simp [TwoPointDiagram.assembleInteractionVertexOrder]

end

end Common
end SecondQuantization
