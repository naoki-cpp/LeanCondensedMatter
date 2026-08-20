import LeanCondensedMatter.Analysis.OrderedSimplex.FamilyShuffleIntegrand
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Ordering.ComponentOrderedSimplex
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
private def TwoPointDiagram.componentInteractionSlotVertexEquiv
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    (Σ B : d.componentPartition.parts, Fin (d.interactionComponentSize B)) ≃
      (Σ B : d.componentPartition.parts,
        ↥(TwoPointDiagram.interactionPart
          (B : Finset (TwoPointVertex S)))) :=
  Equiv.sigmaCongrRight fun B =>
    ((TwoPointDiagram.interactionPart
      (B : Finset (TwoPointVertex S))).orderIsoOfFin rfl).toEquiv

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

/-- Equality of canonical component-local time assignments is exactly equality of ambient times on
all actual interaction vertices of that component. -/
private theorem TwoPointDiagram.canonicalComponentTimeAssignment_eq_iff
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (τ υ : Fin S.card → ℝ) (B : d.componentPartition.parts) :
    d.canonicalComponentInteractionShuffle.timeAssignment τ B =
      d.canonicalComponentInteractionShuffle.timeAssignment υ B ↔
      ∀ v : ↥(TwoPointDiagram.interactionPart
        (B : Finset (TwoPointVertex S))),
        τ ((S.orderIsoOfFin rfl).symm
          (d.interactionVertexComponentEquiv.symm ⟨B, v⟩)) =
        υ ((S.orderIsoOfFin rfl).symm
          (d.interactionVertexComponentEquiv.symm ⟨B, v⟩)) := by
  constructor
  · intro h v
    have hv := congrFun h
      (((TwoPointDiagram.interactionPart
        (B : Finset (TwoPointVertex S))).orderIsoOfFin rfl).symm v)
    simpa [Combinatorics.FamilySlotShuffleTo.timeAssignment,
      TwoPointDiagram.canonicalComponentInteractionShuffle,
      TwoPointDiagram.componentInteractionSlotVertexEquiv] using hv
  · intro h
    funext i
    exact h ((TwoPointDiagram.interactionPart
      (B : Finset (TwoPointVertex S))).orderIsoOfFin rfl i)

/-- For the full finset of `Fin N`, converting the increasing ambient rank back to `Fin N` recovers
the underlying vertex. -/
private theorem finCast_univOrderIsoOfFin_symm
    (x : ↥(Finset.univ : Finset (Fin N))) :
    Fin.cast (by simp)
        (((Finset.univ : Finset (Fin N)).orderIsoOfFin rfl).symm x) = x.1 := by
  let castEmb : Fin (Finset.univ : Finset (Fin N)).card ↪o Fin N :=
    (Fin.castOrderIso (by simp)).toOrderEmbedding
  have hcast : castEmb =
      (Finset.univ : Finset (Fin N)).orderEmbOfFin rfl :=
    Finset.orderEmbOfFin_unique' rfl (fun _ => Finset.mem_univ _)
  have hx := congrArg Subtype.val
    (((Finset.univ : Finset (Fin N)).orderIsoOfFin rfl).apply_symm_apply x)
  change ((Finset.univ : Finset (Fin N)).orderEmbOfFin rfl)
      (((Finset.univ : Finset (Fin N)).orderIsoOfFin rfl).symm x) = x.1 at hx
  rw [← hcast] at hx
  exact hx

/-- For diagrams indexed by all `Fin N` interaction slots, canonical local-time equality is exactly
pointwise equality of the original slot-time functions on the component's interaction vertices. -/
theorem TwoPointDiagram.canonicalComponentTimeAssignment_univ_eq_iff
    (d : TwoPointDiagram ExternalLabel InternalLabel N
      (Finset.univ : Finset (Fin N)))
    (σ υ : Fin N → ℝ) (B : d.componentPartition.parts) :
    d.canonicalComponentInteractionShuffle.timeAssignment
        (fun i => σ (Fin.cast (by simp) i)) B =
      d.canonicalComponentInteractionShuffle.timeAssignment
        (fun i => υ (Fin.cast (by simp) i)) B ↔
      ∀ v : ↥(TwoPointDiagram.interactionPart
        (B : Finset (TwoPointVertex
          (Finset.univ : Finset (Fin N))))),
        σ v.1 = υ v.1 := by
  rw [d.canonicalComponentTimeAssignment_eq_iff]
  have hrank : ∀ v : ↥(TwoPointDiagram.interactionPart
      (B : Finset (TwoPointVertex (Finset.univ : Finset (Fin N))))),
      Fin.cast (by simp)
        (((Finset.univ : Finset (Fin N)).orderIsoOfFin rfl).symm
          (d.interactionVertexComponentEquiv.symm ⟨B, v⟩)) = v.1 := by
    intro v
    calc
      Fin.cast (by simp)
          (((Finset.univ : Finset (Fin N)).orderIsoOfFin rfl).symm
            (d.interactionVertexComponentEquiv.symm ⟨B, v⟩)) =
        (d.interactionVertexComponentEquiv.symm ⟨B, v⟩).1 :=
          finCast_univOrderIsoOfFin_symm _
      _ = v.1 := d.interactionVertexComponentEquiv_symm_val ⟨B, v⟩
  constructor
  · intro h v
    have hv := h v
    rw [hrank v] at hv
    exact hv
  · intro h v
    rw [hrank v]
    exact h v

end

end Common
end SecondQuantization
