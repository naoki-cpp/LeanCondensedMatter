import LeanCondensedMatter.Combinatorics.SlotShuffle
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Core.SlotCongr
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Ordered

set_option linter.style.header false

/-!
# Standardizing vacuum-free external support and the complementary vacuum slots

An external-support fiber whose left slot set has cardinality `m` is carried to
a vacuum-free external diagram over `Fin m`. Its quartic complement is encoded by
the existing ordered quartic diagram equivalence over `Fin k`. Both coordinates
use the increasing slot enumerations; external insertion labels are unchanged.
Multiple externally supported components remain allowed.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {E N M : ℕ}
  {T : Finset (Fin N)} {U : Finset (Fin M)}

/-- Restrict interaction-slot relabeling to diagrams without purely vacuum components. -/
noncomputable def ExternalInsertionDiagram.vacuumFreeSlotCongrEquiv
    (e : ↥T ≃ ↥U) :
    {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N T //
      HasNoVacuumComponent d.vertexGraph} ≃
    {d : ExternalInsertionDiagram ExternalLabel InternalLabel E M U //
      HasNoVacuumComponent d.vertexGraph} :=
  Equiv.subtypeEquiv (ExternalInsertionDiagram.slotCongrEquiv (E := E) e)
    (fun d => (hasNoVacuumComponent_congr_iff
      (d.slotCongrVertexGraphIso (M := M) e) (Equiv.refl (Fin (2 * E))) e
      (fun _ => rfl) (fun _ => rfl)).symm)

/-- Canonically enumerate the interaction slots of a vacuum-free external diagram.
External insertion labels are not reordered. -/
noncomputable def ExternalInsertionDiagram.standardizeVacuumFree
    (T : Finset (Fin N)) {m : ℕ} (h : T.card = m) :
    {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N T //
      HasNoVacuumComponent d.vertexGraph} ≃
    {d : ExternalInsertionDiagram ExternalLabel InternalLabel E m
        (Finset.univ : Finset (Fin m)) //
      HasNoVacuumComponent d.vertexGraph} :=
  ExternalInsertionDiagram.vacuumFreeSlotCongrEquiv
    ((T.orderIsoOfFin h).toEquiv.symm.trans
      (Equiv.subtypeUnivEquiv (fun i : Fin m => Finset.mem_univ i)).symm)

/-- Standardize both halves of a shuffle fiber: vacuum-free external insertions and
ordered quartic vacuum data. The vacuum complement uses the canonical quartic API. -/
noncomputable def ExternalInsertionDiagram.standardizedSupportFiberDataEquiv
    {m k : ℕ} (shuffle : SlotShuffle m k) :
    ({ext : ExternalInsertionDiagram ExternalLabel InternalLabel E (m + k)
          shuffle.leftSlots // HasNoVacuumComponent ext.vertexGraph} ×
      QuarticDiagram InternalLabel (m + k)
        ((Finset.univ : Finset (Fin (m + k))) \ shuffle.leftSlots)) ≃
    ({ext : ExternalInsertionDiagram ExternalLabel InternalLabel E m
          (Finset.univ : Finset (Fin m)) //
          HasNoVacuumComponent ext.vertexGraph} ×
      OrderedQuarticDiagramData InternalLabel k) :=
  Equiv.prodCongr
    (ExternalInsertionDiagram.standardizeVacuumFree
      shuffle.leftSlots shuffle.card_leftSlots)
    (quarticDiagramEquivOrderedData shuffle.sdiffLeftSlotsOrderEquiv)

end Common
end SecondQuantization
