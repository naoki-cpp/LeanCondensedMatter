import LeanCondensedMatter.Combinatorics.FamilySlotShuffle
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Components.ComponentVertexProduct

set_option linter.style.header false

/-!
# Component interaction shuffles of two-point diagrams

A two-point diagram's full connected components partition its interaction vertices through their
interaction parts. This module keeps only the resulting component-size family and the corresponding
order-preserving family-shuffle type. Coordinate restriction, shuffled products, and ordered-simplex
factorization are owned directly by `Combinatorics.FamilySlotShuffleTo` and
`Analysis/OrderedSimplex`.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

noncomputable section

/-- Number of interaction slots belonging to one full component. -/
abbrev TwoPointDiagram.interactionComponentSize {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) : ℕ :=
  (TwoPointDiagram.interactionPart
    (B : Finset (TwoPointVertex S))).card

/-- An order-preserving interleaving of all component-local interaction slots into the ambient
interaction slots. -/
abbrev TwoPointDiagram.ComponentInteractionShuffle {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :=
  Combinatorics.FamilySlotShuffleTo d.interactionComponentSize S.card

end

end Common
end SecondQuantization
