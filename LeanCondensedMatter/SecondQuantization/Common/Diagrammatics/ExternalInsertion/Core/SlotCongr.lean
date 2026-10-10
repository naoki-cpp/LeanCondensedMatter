import LeanCondensedMatter.Combinatorics.PerfectPairing.Transport
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

variable {ExternalLabel InternalLabel : Type*} {E N M : ℕ}
  {T : Finset (Fin N)} {U : Finset (Fin M)}

/-- Relabeling the interaction vertices relabels the external-insertion vertices. -/
def externalInsertionVertexCongr (e : ↥T ≃ ↥U) : ExternalInsertionVertex E T ≃ ExternalInsertionVertex E U :=
  Equiv.sumCongr (Equiv.refl (Fin (2 * E))) e

@[simp]
theorem externalInsertionVertexCongr_inl (e : ↥T ≃ ↥U) (a : Fin (2 * E)) :
    externalInsertionVertexCongr (E := E) e (Sum.inl a) = Sum.inl a := rfl

@[simp]
theorem externalInsertionVertexCongr_inr (e : ↥T ≃ ↥U) (v : ↥T) :
    externalInsertionVertexCongr (E := E) e (Sum.inr v) = Sum.inr (e v) := rfl

/-- Relabeling the interaction vertices relabels the unflattened legs. -/
def externalInsertionLegDataCongr (e : ↥T ≃ ↥U) : ExternalInsertionLeg E T ≃ ExternalInsertionLeg E U :=
  Equiv.sumCongr (Equiv.refl (Fin (2 * E))) (e.prodCongr (Equiv.refl (Fin 4)))

@[simp]
theorem externalInsertionLegDataCongr_inl (e : ↥T ≃ ↥U) (a : Fin (2 * E)) :
    externalInsertionLegDataCongr (E := E) e (Sum.inl a) = Sum.inl a := rfl

@[simp]
theorem externalInsertionLegDataCongr_inr (e : ↥T ≃ ↥U) (v : ↥T) (l : Fin 4) :
    externalInsertionLegDataCongr (E := E) e (Sum.inr (v, l)) = Sum.inr (e v, l) := rfl

/-- Relabeling the interaction vertices relabels the flattened legs. -/
noncomputable def externalInsertionLegCongr (e : ↥T ≃ ↥U) :
    Fin (2 * (2 * T.card + E)) ≃ Fin (2 * (2 * U.card + E)) :=
  (externalInsertionLegEquiv E T).trans
    ((Equiv.sumCongr (Equiv.refl (Fin (2 * E))) (e.prodCongr (Equiv.refl (Fin 4)))).trans
      (externalInsertionLegEquiv E U).symm)

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

@[simp]
theorem ExternalInsertionDiagram.slotCongr_vertexLabel (e : ↥T ≃ ↥U)
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N T) (v : ↥U) :
    (d.slotCongr (M := M) e).vertexLabel v = d.vertexLabel (e.symm v) := rfl

/-- The transported pairing pairs the transported legs. -/
theorem ExternalInsertionDiagram.slotCongr_partner (e : ↥T ≃ ↥U)
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N T)
    (leg : Fin (2 * (2 * T.card + E))) :
    (d.slotCongr (M := M) e).pairing.partner (externalInsertionLegCongr (E := E) e leg) =
      externalInsertionLegCongr (E := E) e (d.pairing.partner leg) := by
  simp [ExternalInsertionDiagram.slotCongr]

/-- **The transport is an isomorphism of vertex graphs.** -/
theorem ExternalInsertionDiagram.slotCongr_adj_iff (e : ↥T ≃ ↥U)
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N T) (v w : ExternalInsertionVertex E T) :
    (d.slotCongr (M := M) e).vertexGraph.Adj
        (externalInsertionVertexCongr (E := E) e v) (externalInsertionVertexCongr (E := E) e w) ↔
      d.vertexGraph.Adj v w := by
  constructor
  · rintro ⟨hne, leg, hleg, hpartner⟩
    obtain ⟨leg, rfl⟩ := (externalInsertionLegCongr (E := E) e).surjective leg
    rw [externalInsertionVertexOfLeg_externalInsertionLegCongr] at hleg
    rw [d.slotCongr_partner e leg, externalInsertionVertexOfLeg_externalInsertionLegCongr] at hpartner
    exact ⟨fun hvw => hne (congrArg (externalInsertionVertexCongr (E := E) e) hvw), leg,
      (externalInsertionVertexCongr (E := E) e).injective hleg, (externalInsertionVertexCongr (E := E) e).injective hpartner⟩
  · rintro ⟨hne, leg, hleg, hpartner⟩
    refine ⟨fun hEq => hne ((externalInsertionVertexCongr (E := E) e).injective hEq), externalInsertionLegCongr (E := E) e leg, ?_, ?_⟩
    · rw [externalInsertionVertexOfLeg_externalInsertionLegCongr, hleg]
    · rw [d.slotCongr_partner e leg, externalInsertionVertexOfLeg_externalInsertionLegCongr, hpartner]

/-- Interaction-slot relabeling induces an isomorphism of vertex graphs. -/
noncomputable def ExternalInsertionDiagram.slotCongrVertexGraphIso (e : ↥T ≃ ↥U)
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N T) :
    d.vertexGraph ≃g (d.slotCongr (M := M) e).vertexGraph where
  toEquiv := externalInsertionVertexCongr (E := E) e
  map_rel_iff' := by
    intro a b
    exact d.slotCongr_adj_iff (M := M) e a b

/-- **Reachability is preserved by the transport.** -/
theorem ExternalInsertionDiagram.slotCongr_reachable_iff (e : ↥T ≃ ↥U)
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N T) (v w : ExternalInsertionVertex E T) :
    (d.slotCongr (M := M) e).vertexGraph.Reachable
        (externalInsertionVertexCongr (E := E) e v) (externalInsertionVertexCongr (E := E) e w) ↔
      d.vertexGraph.Reachable v w := by
  exact SimpleGraph.Iso.reachable_iff
    (φ := d.slotCongrVertexGraphIso (M := M) e) (u := v) (v := w)

/-- **Absence of vacuum components is preserved by the transport.** -/
theorem ExternalInsertionDiagram.slotCongr_hasNoVacuumComponent_iff (e : ↥T ≃ ↥U)
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N T) :
    HasNoVacuumComponent (d.slotCongr (M := M) e).vertexGraph ↔ HasNoVacuumComponent d.vertexGraph := by
  constructor
  · intro hd v
    obtain ⟨f, hf⟩ := hd (e v)
    refine ⟨f, ?_⟩
    rw [← d.slotCongr_reachable_iff (M := M) e (Sum.inl f) (Sum.inr v)]
    simpa using hf
  · intro hd v
    obtain ⟨f, hf⟩ := hd (e.symm v)
    refine ⟨f, ?_⟩
    have := (d.slotCongr_reachable_iff (M := M) e (Sum.inl f) (Sum.inr (e.symm v))).2 hf
    simpa using this


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

end Common
end SecondQuantization
