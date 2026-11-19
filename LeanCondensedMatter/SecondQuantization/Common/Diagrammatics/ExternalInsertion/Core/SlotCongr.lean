import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Core.Diagram
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalComponents

set_option linter.style.header false

/-!
# Interaction-slot relabeling for arbitrary external insertions

A relabeling changes the quartic interaction slots while leaving all `2 * E` external
insertions and their labels fixed. It transports the flattened-leg pairing through the
canonical external-first leg enumeration. The induced vertex-graph equivalence preserves
reachability and absence of purely vacuum components.
-/

namespace SecondQuantization
namespace Common

open Combinatorics
open scoped BigOperators

variable {ExternalLabel InternalLabel : Type*} {E N M : ℕ}
  {T : Finset (Fin N)} {U : Finset (Fin M)}

/-- Relabeling the interaction vertices relabels the external-insertion vertices. -/
def externalInsertionVertexCongr (e : ↥T ≃ ↥U) : ExternalInsertionVertex E T ≃ ExternalInsertionVertex E U :=
  Equiv.sumCongr (Equiv.refl (Fin (2 * E))) e

/-- Relabeling the interaction vertices relabels the flattened legs. -/
noncomputable def externalInsertionLegCongr (e : ↥T ≃ ↥U) :
    Fin (2 * (2 * T.card + E)) ≃ Fin (2 * (2 * U.card + E)) :=
  (externalInsertionLegEquiv E T).trans
    ((Equiv.sumCongr (Equiv.refl (Fin (2 * E))) (e.prodCongr (Equiv.refl (Fin 4)))).trans
      (externalInsertionLegEquiv E U).symm)

/-- Composing two exact interaction-slot relabelings of the flattened
fermionic legs is the relabeling along the composite slot equivalence.
This keeps external insertion labels and each local quartic-leg number
fixed, so it does not assume any order-dependent pairing sign. -/
theorem externalInsertionLegCongr_trans
    {V : ℕ} {W : Finset (Fin V)}
    (e : ↥T ≃ ↥U) (f : ↥U ≃ ↥W) :
    externalInsertionLegCongr (E := E) (e.trans f) =
      (externalInsertionLegCongr (E := E) e).trans
        (externalInsertionLegCongr (E := E) f) := by
  apply Equiv.ext
  intro p
  obtain ⟨x, rfl⟩ := (externalInsertionLegEquiv E T).symm.surjective p
  cases x with
  | inl i => simp [externalInsertionLegCongr]
  | inr v =>
      obtain ⟨i, j⟩ := v
      simp [externalInsertionLegCongr]

/-- The inverse relabeling of legs is the relabeling along the inverse. -/
theorem externalInsertionLegCongr_symm (e : ↥T ≃ ↥U) :
    externalInsertionLegCongr (E := E) e.symm = (externalInsertionLegCongr (E := E) e).symm := by
  refine Equiv.ext fun leg => ?_
  obtain ⟨x, rfl⟩ := (externalInsertionLegEquiv E U).symm.surjective leg
  cases x with
  | inl a => simp [externalInsertionLegCongr]
  | inr p =>
      obtain ⟨v, l⟩ := p
      simp [externalInsertionLegCongr]

/-- The relabeled leg carries the relabeled vertex. -/
theorem externalInsertionVertexOfLeg_externalInsertionLegCongr (e : ↥T ≃ ↥U)
    (leg : Fin (2 * (2 * T.card + E))) :
    externalInsertionVertexOfLeg (externalInsertionLegCongr (E := E) e leg) =
      externalInsertionVertexCongr (E := E) e (externalInsertionVertexOfLeg leg) := by
  obtain ⟨x, rfl⟩ := (externalInsertionLegEquiv E T).symm.surjective leg
  cases x with
  | inl a => simp [externalInsertionLegCongr, externalInsertionVertexOfLeg, externalInsertionVertexCongr]
  | inr p =>
      obtain ⟨v, l⟩ := p
      simp [externalInsertionLegCongr, externalInsertionVertexOfLeg, externalInsertionVertexCongr]

/-- **Transport an external-insertion diagram along a relabeling of its interaction vertices.** -/
noncomputable def ExternalInsertionDiagram.slotCongr (e : ↥T ≃ ↥U)
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N T) :
    ExternalInsertionDiagram ExternalLabel InternalLabel E M U where
  externalLabel := d.externalLabel
  vertexLabel v := d.vertexLabel (e.symm v)
  pairing := d.pairing.transport (externalInsertionLegCongr (E := E) e).symm

@[simp]
theorem ExternalInsertionDiagram.slotCongr_externalLabel (e : ↥T ≃ ↥U)
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N T) :
    (d.slotCongr (M := M) e).externalLabel = d.externalLabel := rfl

/-- The physical Wick pairing partner is exactly conjugated by the
induced flattened-leg equivalence under *any* interaction-slot
relabeling. It transports the two endpoints together, without
asserting that their normalized increasing order is preserved. -/
theorem ExternalInsertionDiagram.slotCongr_pairing_partner
    (e : ↥T ≃ ↥U)
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N T)
    (p : Fin (2 * (2 * T.card + E))) :
    (d.slotCongr e).pairing.partner
        (externalInsertionLegCongr (E := E) e p) =
      externalInsertionLegCongr (E := E) e (d.pairing.partner p) := by
  simp [ExternalInsertionDiagram.slotCongr, PairingOn.transport_partner]

/-- Relabeling interaction slots preserves every commutative product of vertex weights.
The result does not depend on any fermionic or time-ordering conventions. -/
theorem ExternalInsertionDiagram.slotCongr_vertexWeight
    {M : Type*} [CommMonoid M] (e : ↥T ≃ ↥U)
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N T)
    (w : InternalLabel → M) :
    (d.slotCongr e).vertexWeight w = d.vertexWeight w := by
  classical
  change (∏ v : ↥U, w (d.vertexLabel (e.symm v))) =
    ∏ v : ↥T, w (d.vertexLabel v)
  exact Equiv.prod_comp e.symm (fun v : ↥T => w (d.vertexLabel v))

/-- The full labelled Wick diagram transport is functorial: relabeling
interaction vertices in two stages has exactly the same external labels,
quartic labels, and Wick pairing partners as one composite relabeling. -/
theorem ExternalInsertionDiagram.slotCongr_trans
    {V : ℕ} {W : Finset (Fin V)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N T)
    (e : ↥T ≃ ↥U) (f : ↥U ≃ ↥W) :
    (d.slotCongr e).slotCongr f = d.slotCongr (e.trans f) := by
  apply ExternalInsertionDiagram.ext
  · rfl
  · funext v
    simp [ExternalInsertionDiagram.slotCongr]
  · change
      (d.pairing.transport (externalInsertionLegCongr (E := E) e).symm).transport
          (externalInsertionLegCongr (E := E) f).symm =
        d.pairing.transport (externalInsertionLegCongr (E := E) (e.trans f)).symm
    rw [Combinatorics.PairingOn.transport_trans, externalInsertionLegCongr_trans]
    rfl

/-- Interaction-slot relabeling induces an isomorphism of vertex graphs. -/
noncomputable def ExternalInsertionDiagram.slotCongrVertexGraphIso (e : ↥T ≃ ↥U)
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N T) :
    d.vertexGraph ≃g (d.slotCongr (M := M) e).vertexGraph :=
  d.pairing.vertexGraphTransportIso (externalInsertionLegCongr (E := E) e)
    (externalInsertionVertexOfLeg (E := E) (S := T))
    (externalInsertionVertexOfLeg (E := E) (S := U))
    (externalInsertionVertexCongr (E := E) e)
    (externalInsertionVertexOfLeg_externalInsertionLegCongr e)

/-- The actual external-source connected-component partition is
invariant when arbitrary quartic interaction vertices are relabeled.
This strengthens reachability invariance to equality of the **entire
partition** over the same fixed external insertion slots. -/
theorem ExternalInsertionDiagram.slotCongr_externalComponentPartition
    (e : ↥T ≃ ↥U)
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N T) :
    externalComponentPartition (d.slotCongr (M := M) e).vertexGraph =
      externalComponentPartition d.vertexGraph := by
  classical
  exact externalComponentPartition_congr_of_external_fixed
    (d.slotCongrVertexGraphIso (M := M) e) (fun _ => rfl)

/-- The transport is an equivalence of diagram types. -/
noncomputable def ExternalInsertionDiagram.slotCongrEquiv (e : ↥T ≃ ↥U) :
    ExternalInsertionDiagram ExternalLabel InternalLabel E N T ≃
      ExternalInsertionDiagram ExternalLabel InternalLabel E M U where
  toFun d := d.slotCongr e
  invFun d := d.slotCongr e.symm
  left_inv d := by
    refine ExternalInsertionDiagram.ext rfl (funext fun v => ?_) ?_
    · simp [ExternalInsertionDiagram.slotCongr]
    · change (d.pairing.transport (externalInsertionLegCongr (E := E) e).symm).transport
        (externalInsertionLegCongr (E := E) e.symm).symm = d.pairing
      rw [externalInsertionLegCongr_symm]
      simp
  right_inv d := by
    refine ExternalInsertionDiagram.ext rfl (funext fun v => ?_) ?_
    · simp [ExternalInsertionDiagram.slotCongr]
    · change (d.pairing.transport (externalInsertionLegCongr (E := E) e.symm).symm).transport
        (externalInsertionLegCongr (E := E) e).symm = d.pairing
      rw [externalInsertionLegCongr_symm]
      simp

/-- Arbitrary interaction-slot relabeling preserves preconnectedness
of the *entire* Wick vertex graph. This includes local blocks with no
interaction vertices. No order-preservation assumption on the vertex
relabeling is needed for this graph-theoretic statement. -/
theorem ExternalInsertionDiagram.slotCongr_preconnected_iff
    (e : ↥T ≃ ↥U)
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N T) :
    (d.slotCongr (M := M) e).vertexGraph.Preconnected ↔
      d.vertexGraph.Preconnected :=
  (d.slotCongrVertexGraphIso (M := M) e).preconnected_iff.symm

/-- A concrete equivalence between the preconnected local Wick-diagram
fibers under an arbitrary bijective interaction-slot relabeling. This is
the structural transport needed to compare independent connected
blocks belonging to different physical owner assignments of the same
interaction cardinalities. In particular, it does not insert an
additional permutation or multiplicity of local pairings. -/
noncomputable def ExternalInsertionDiagram.preconnectedSlotCongrEquiv
    (e : ↥T ≃ ↥U) :
    {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N T //
      d.vertexGraph.Preconnected} ≃
    {d : ExternalInsertionDiagram ExternalLabel InternalLabel E M U //
      d.vertexGraph.Preconnected} :=
  Equiv.subtypeEquiv
    (ExternalInsertionDiagram.slotCongrEquiv (E := E) e)
    (fun d => (d.slotCongr_preconnected_iff (M := M) e).symm)

open Classical in
/-- Finite sums over preconnected Wick diagrams are invariant under
bijective interaction-slot relabeling, provided the diagram weight is
transported together with the diagram. This is the exact algebraic
sum-reindexing needed to compare different physical interaction-owner
fibers after canonical local standardization. It does not assume
invariance of the ordered Dyson integrand under a nonmonotone
interaction permutation. -/
theorem ExternalInsertionDiagram.sum_preconnectedSlotCongr
    [Fintype ExternalLabel] [Fintype InternalLabel]
    {R : Type*} [AddCommMonoid R]
    (e : ↥T ≃ ↥U)
    (weight : ExternalInsertionDiagram ExternalLabel InternalLabel E M U → R) :
    (∑ d : {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N T //
        d.vertexGraph.Preconnected}, weight (d.1.slotCongr e)) =
      ∑ d : {d : ExternalInsertionDiagram ExternalLabel InternalLabel E M U //
        d.vertexGraph.Preconnected}, weight d.1 := by
  classical
  let φ := ExternalInsertionDiagram.preconnectedSlotCongrEquiv
    (E := E) (ExternalLabel := ExternalLabel) (InternalLabel := InternalLabel) e
  change (∑ d : {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N T //
      d.vertexGraph.Preconnected}, weight (φ d).1) =
    ∑ d : {d : ExternalInsertionDiagram ExternalLabel InternalLabel E M U //
      d.vertexGraph.Preconnected}, weight d.1
  exact Equiv.sum_comp φ (fun d => weight d.1)

end Common
end SecondQuantization
