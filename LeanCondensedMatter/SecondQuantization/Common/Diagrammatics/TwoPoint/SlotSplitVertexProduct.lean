import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotCongr
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotLegSplitting

set_option linter.style.header false

/-!
# Vertex-label products across the slot split

The amplitude of a two-point diagram carries one coupling factor per interaction vertex. Factorizing
an amplitude along the external/vacuum split therefore needs the corresponding factorization of that
product, and transporting a piece to standard slot indexing needs the product to be unchanged.

Both are pure reindexing: `Combinatorics.subsetSumSdiffEquiv` presents the ambient vertices as the
two blocks, and `TwoPointDiagram.slotCongr` renames vertices along an equivalence. Neither statement
involves times, pairings, or connectivity.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {N M : ℕ}
variable {R : Type*} [CommMonoid R]

/-- The vertex-label product is unchanged by transporting the diagram along a relabeling of its
interaction vertices. -/
theorem TwoPointDiagram.prod_vertexLabel_slotCongr {T : Finset (Fin N)} {U : Finset (Fin M)}
    (e : ↥T ≃ ↥U) (d : TwoPointDiagram ExternalLabel InternalLabel N T)
    (f : InternalLabel → R) :
    (∏ v : ↥U, f ((d.slotCongr (M := M) e).vertexLabel v)) =
      ∏ v : ↥T, f (d.vertexLabel v) := by
  rw [← Equiv.prod_comp e fun v => f ((d.slotCongr (M := M) e).vertexLabel v)]
  exact Finset.prod_congr rfl fun v _ => by
    simp [TwoPointDiagram.slotCongr]

/-- **The vertex-label product of a reassembled diagram splits into the two pieces.** -/
theorem TwoPointDiagram.prod_vertexLabel_ofSlotSplit {S T : Finset (Fin N)} (h : T ⊆ S)
    (ext : TwoPointDiagram ExternalLabel InternalLabel N T)
    (vac : QuarticDiagram InternalLabel N (S \ T)) (f : InternalLabel → R) :
    (∏ v : ↥S, f ((TwoPointDiagram.ofSlotSplit h ext vac).vertexLabel v)) =
      (∏ v : ↥T, f (ext.vertexLabel v)) * ∏ v : ↥(S \ T), f (vac.vertexLabel v) := by
  classical
  rw [← Equiv.prod_comp (Combinatorics.subsetSumSdiffEquiv h)
      fun v => f ((TwoPointDiagram.ofSlotSplit h ext vac).vertexLabel v),
    Fintype.prod_sum_type]
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun a _ => ?_)
    (Finset.prod_congr rfl fun b _ => ?_)
  · exact congrArg f (TwoPointDiagram.ofSlotSplit_vertexLabel_of_mem h ext vac _ a.2)
  · exact congrArg f (TwoPointDiagram.ofSlotSplit_vertexLabel_of_not_mem h ext vac _
      (Finset.mem_sdiff.mp b.2).2)

end Common
end SecondQuantization
