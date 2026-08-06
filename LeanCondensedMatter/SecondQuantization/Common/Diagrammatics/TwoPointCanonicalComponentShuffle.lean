import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPointComponentOrderedSimplex
import Mathlib.Data.Finset.Sort

set_option linter.style.header false

/-!
# Canonical interaction-component shuffle of a two-point diagram

The abstract component-shuffle type contains every order-preserving interleaving of the local
interaction slots.  For locality of the fixed diagram amplitude, one distinguished shuffle is
needed: the shuffle induced by the interaction vertices as they occur in the original ambient
vertex order.

This module constructs that canonical shuffle.  Local slots enumerate each component's interaction
part increasingly, and the ambient slots enumerate the original interaction finset increasingly.
It also characterizes equality of canonical component-local time assignments directly as equality
of the ambient times on all interaction vertices of that component.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

noncomputable section

/-- Component-local ordered slots are equivalent to the actual interaction vertices carried by
those components. -/
def TwoPointDiagram.componentInteractionSlotVertexEquiv
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    (Σ B : d.componentPartition.parts, Fin (d.interactionComponentSize B)) ≃
      (Σ B : d.componentPartition.parts,
        ↥(TwoPointDiagram.interactionPart
          (B : Finset (TwoPointVertex S)))) where
  toFun x :=
    ⟨x.1, (TwoPointDiagram.interactionPart
      (x.1 : Finset (TwoPointVertex S))).orderIsoOfFin rfl x.2⟩
  invFun x :=
    ⟨x.1, ((TwoPointDiagram.interactionPart
      (x.1 : Finset (TwoPointVertex S))).orderIsoOfFin rfl).symm x.2⟩
  left_inv x := by
    rcases x with ⟨B, i⟩
    simp
  right_inv x := by
    rcases x with ⟨B, v⟩
    simp

@[simp]
theorem TwoPointDiagram.componentInteractionSlotVertexEquiv_apply
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) (i : Fin (d.interactionComponentSize B)) :
    d.componentInteractionSlotVertexEquiv ⟨B, i⟩ =
      ⟨B, (TwoPointDiagram.interactionPart
        (B : Finset (TwoPointVertex S))).orderIsoOfFin rfl i⟩ :=
  rfl

@[simp]
theorem TwoPointDiagram.componentInteractionSlotVertexEquiv_symm_apply
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts)
    (v : ↥(TwoPointDiagram.interactionPart
      (B : Finset (TwoPointVertex S)))) :
    d.componentInteractionSlotVertexEquiv.symm ⟨B, v⟩ =
      ⟨B, ((TwoPointDiagram.interactionPart
        (B : Finset (TwoPointVertex S))).orderIsoOfFin rfl).symm v⟩ :=
  rfl

/-- The component interaction shuffle induced by the original ambient interaction-vertex order. -/
def TwoPointDiagram.canonicalComponentInteractionShuffle
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    d.ComponentInteractionShuffle where
  slotEquiv :=
    d.componentInteractionSlotVertexEquiv.trans
      (d.interactionVertexComponentEquiv.symm.trans
        ((S.orderIsoOfFin rfl).symm.toEquiv))
  strictMono := by
    intro B a b hab
    apply (S.orderIsoOfFin rfl).symm.strictMono
    change
      (d.interactionVertexComponentEquiv.symm
        ⟨B, (TwoPointDiagram.interactionPart
          (B : Finset (TwoPointVertex S))).orderIsoOfFin rfl a⟩ : ↥S) <
      d.interactionVertexComponentEquiv.symm
        ⟨B, (TwoPointDiagram.interactionPart
          (B : Finset (TwoPointVertex S))).orderIsoOfFin rfl b⟩
    change
      ((TwoPointDiagram.interactionPart
        (B : Finset (TwoPointVertex S))).orderIsoOfFin rfl a :
          ↥(TwoPointDiagram.interactionPart
            (B : Finset (TwoPointVertex S)))) <
      (TwoPointDiagram.interactionPart
        (B : Finset (TwoPointVertex S))).orderIsoOfFin rfl b
    exact (TwoPointDiagram.interactionPart
      (B : Finset (TwoPointVertex S))).orderIsoOfFin rfl |>.strictMono hab

@[simp]
theorem TwoPointDiagram.canonicalComponentInteractionShuffle_slotEquiv_apply
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) (i : Fin (d.interactionComponentSize B)) :
    d.canonicalComponentInteractionShuffle.slotEquiv ⟨B, i⟩ =
      (S.orderIsoOfFin rfl).symm
        (d.interactionVertexComponentEquiv.symm
          ⟨B, (TwoPointDiagram.interactionPart
            (B : Finset (TwoPointVertex S))).orderIsoOfFin rfl i⟩) :=
  rfl

/-- The local ordered slot occupied by one actual interaction vertex of a component. -/
def TwoPointDiagram.interactionComponentSlotOfVertex
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts)
    (v : ↥(TwoPointDiagram.interactionPart
      (B : Finset (TwoPointVertex S)))) :
    Fin (d.interactionComponentSize B) :=
  ((TwoPointDiagram.interactionPart
    (B : Finset (TwoPointVertex S))).orderIsoOfFin rfl).symm v

@[simp]
theorem TwoPointDiagram.canonicalComponentInteractionShuffle_slotOfVertex
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts)
    (v : ↥(TwoPointDiagram.interactionPart
      (B : Finset (TwoPointVertex S)))) :
    d.canonicalComponentInteractionShuffle.slotEquiv
        ⟨B, d.interactionComponentSlotOfVertex B v⟩ =
      (S.orderIsoOfFin rfl).symm
        (d.interactionVertexComponentEquiv.symm ⟨B, v⟩) := by
  simp [TwoPointDiagram.interactionComponentSlotOfVertex]

/-- Equality of canonical component-local time assignments is exactly equality of ambient times on
all actual interaction vertices of that component. -/
theorem TwoPointDiagram.canonicalComponentTimeAssignment_eq_iff
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (τ υ : Fin S.card → ℝ) (B : d.componentPartition.parts) :
    d.interactionComponentTimeAssignment
        d.canonicalComponentInteractionShuffle τ B =
      d.interactionComponentTimeAssignment
        d.canonicalComponentInteractionShuffle υ B ↔
      ∀ v : ↥(TwoPointDiagram.interactionPart
        (B : Finset (TwoPointVertex S))),
        τ ((S.orderIsoOfFin rfl).symm
          (d.interactionVertexComponentEquiv.symm ⟨B, v⟩)) =
        υ ((S.orderIsoOfFin rfl).symm
          (d.interactionVertexComponentEquiv.symm ⟨B, v⟩)) := by
  constructor
  · intro h v
    have hv := congrFun h (d.interactionComponentSlotOfVertex B v)
    simpa using hv
  · intro h
    funext i
    exact h ((TwoPointDiagram.interactionPart
      (B : Finset (TwoPointVertex S))).orderIsoOfFin rfl i)

end

end Common
end SecondQuantization
