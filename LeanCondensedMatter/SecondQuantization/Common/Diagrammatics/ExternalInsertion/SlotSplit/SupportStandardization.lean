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

/-- The increasing support-slot standardization preserves the actual flattened
leg positions. Neither the external legs nor the internal four-leg blocks are
permuted within their sectors. -/
theorem externalInsertionLegCongr_standardize
    (T : Finset (Fin N)) :
    externalInsertionLegCongr (E := E)
      ((T.orderIsoOfFin rfl).toEquiv.symm.trans
        (Equiv.subtypeUnivEquiv
          (fun i : Fin T.card => Finset.mem_univ i)).symm) =
      finCongr (by simp) := by
  classical
  apply Equiv.ext
  intro p
  obtain ⟨x, rfl⟩ := (externalInsertionLegEquiv E T).symm.surjective p
  cases x with
  | inl e =>
      simp only [externalInsertionLegCongr, Equiv.trans_apply,
        Equiv.apply_symm_apply, Equiv.sumCongr_apply, Sum.map_inl,
        Equiv.refl_apply]
      apply Fin.ext
      change (externalInsertionExternalLeg E
          (Finset.univ : Finset (Fin T.card)) e).val =
        (Fin.cast rfl (externalInsertionExternalLeg E T e)).val
      simp only [Fin.val_cast, externalInsertionExternalLeg_val]
  | inr vl =>
      rcases vl with ⟨v, l⟩
      simp only [externalInsertionLegCongr, Equiv.trans_apply,
        Equiv.apply_symm_apply, Equiv.sumCongr_apply, Sum.map_inr,
        Equiv.prodCongr_apply, Equiv.refl_apply]
      let vFin : Fin T.card := (T.orderIsoOfFin rfl).symm v
      apply Fin.ext
      change (externalInsertionInteractionLeg (E := E)
          (⟨vFin, Finset.mem_univ vFin⟩ :
            ↥(Finset.univ : Finset (Fin T.card))) l).val =
        (Fin.cast rfl (externalInsertionInteractionLeg (E := E) v l)).val
      simp only [Fin.val_cast, externalInsertionInteractionLeg_val]
      have huniv :
          (((Finset.univ : Finset (Fin T.card)).orderIsoOfFin rfl).symm
            (⟨vFin, Finset.mem_univ vFin⟩ :
              ↥(Finset.univ : Finset (Fin T.card)))).val = vFin.val := by
        rw [Finset.orderIsoOfFin_symm_apply, Fin.sort_univ, List.idxOf_finRange]
      rw [huniv]
      rfl

/-- The pairing of a canonically reindexed support diagram is the original
pairing transported only by the canonical type-level cast of its pair count. -/
theorem ExternalInsertionDiagram.standardize_pairing
    (T : Finset (Fin N))
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N T) :
    (d.slotCongr
      ((T.orderIsoOfFin rfl).toEquiv.symm.trans
        (Equiv.subtypeUnivEquiv
          (fun i : Fin T.card => Finset.mem_univ i)).symm)).pairing =
      d.pairing.transport (finCongr (by simp)).symm := by
  classical
  change d.pairing.transport
    (externalInsertionLegCongr (E := E)
      ((T.orderIsoOfFin rfl).toEquiv.symm.trans
        (Equiv.subtypeUnivEquiv
          (fun i : Fin T.card => Finset.mem_univ i)).symm)).symm =
      d.pairing.transport (finCongr (by simp)).symm
  rw [externalInsertionLegCongr_standardize]

/-- The standalone vacuum-free support diagram has the same vertex-weight product
as the original support diagram, independent of the gaps in the ambient slots. -/
theorem ExternalInsertionDiagram.standardizeVacuumFree_vertexWeight
    {MWeight : Type*} [CommMonoid MWeight] (T : Finset (Fin N))
    (d : {ext : ExternalInsertionDiagram ExternalLabel InternalLabel E N T //
      HasNoVacuumComponent ext.vertexGraph}) (w : InternalLabel → MWeight) :
    ((ExternalInsertionDiagram.standardizeVacuumFree T rfl) d).1.vertexWeight w =
      d.1.vertexWeight w := by
  classical
  change (d.1.slotCongr
    ((T.orderIsoOfFin rfl).toEquiv.symm.trans
      (Equiv.subtypeUnivEquiv
        (fun i : Fin T.card => Finset.mem_univ i)).symm)).vertexWeight w =
      d.1.vertexWeight w
  exact d.1.slotCongr_vertexWeight _ w

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
