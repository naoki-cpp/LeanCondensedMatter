import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Ordered
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ExternalConnectivity
import LeanCondensedMatter.Combinatorics.PerfectPairing.VertexGraphRelabel

set_option linter.style.header false

/-!
# Connectivity under interaction-vertex ordering

Reindexing a finite two-point diagram from an arbitrary interaction set to explicit ordered slots is
a graph isomorphism: external vertices are fixed and interaction vertices are transported by the
chosen vertex order. Consequently external connectedness and the no-vacuum-component condition are
unchanged by the reindexing used in the Dyson expansion.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

/-- Explicit ordered vertices mapped back to the ambient interaction vertices selected by `order`. -/
def twoPointInteractionOrderVertexEquiv {S : Finset (Fin N)}
    (order : QuarticVertexOrder S) :
    TwoPointVertex (Finset.univ : Finset (Fin S.card)) ≃ TwoPointVertex S :=
  Equiv.sumCongr (Equiv.refl (Fin 2))
    ((finEquivUnivSubtype S.card).symm.trans order)

/-- Incident vertex of one flattened explicit ordered leg, with the cardinality normalization kept
local to this definition. -/
noncomputable def orderedTwoPointVertexOfLeg (n : ℕ)
    (leg : Fin (2 * (2 * n + 1))) :
    TwoPointVertex (Finset.univ : Finset (Fin n)) :=
  twoPointVertexOfLeg (Fin.cast (by simp) leg)

/-- The ordered leg permutation and the ordered vertex permutation commute with the incidence map. -/
theorem twoPointVertexOfLeg_orderedTwoPointLegToDiagramLeg
    {S : Finset (Fin N)} (order : QuarticVertexOrder S)
    (leg : Fin (2 * (2 * S.card + 1))) :
    twoPointVertexOfLeg (orderedTwoPointLegToDiagramLeg order leg) =
      twoPointInteractionOrderVertexEquiv order
        (orderedTwoPointVertexOfLeg S.card leg) := by
  unfold orderedTwoPointVertexOfLeg twoPointVertexOfLeg
  simp only [orderedTwoPointLegToDiagramLeg, Equiv.trans_apply, Equiv.apply_symm_apply]
  have hcast :
      (finCongr (by simp) leg :
        Fin (2 * (2 * (Finset.univ : Finset (Fin S.card)).card + 1))) =
      Fin.cast (by simp) leg := by
    apply Fin.ext
    rfl
  rw [hcast]
  generalize hleg :
      twoPointLegEquiv (Finset.univ : Finset (Fin S.card)) (Fin.cast (by simp) leg) = x
  rcases x with e | ⟨v, l⟩
  · rw [hleg]
    rfl
  · rw [hleg]
    rfl

/-- The vertex graph of a pairing transported to one interaction order is isomorphic to the
original diagram vertex graph. -/
theorem TwoPointDiagram.pairingInInteractionOrder_reachable_iff
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S)
    (v w : TwoPointVertex (Finset.univ : Finset (Fin S.card))) :
    ((d.pairingInInteractionOrder order).vertexGraph
      (orderedTwoPointVertexOfLeg S.card)).Reachable v w ↔
      d.vertexGraph.Reachable
        (twoPointInteractionOrderVertexEquiv order v)
        (twoPointInteractionOrderVertexEquiv order w) := by
  exact d.pairing.vertexGraph_relabel_reachable_iff
    (orderedTwoPointLegToDiagramLeg order)
    (twoPointInteractionOrderVertexEquiv order)
    twoPointVertexOfLeg (orderedTwoPointVertexOfLeg S.card)
    (twoPointVertexOfLeg_orderedTwoPointLegToDiagramLeg order) v w

private theorem orderedTwoPointPairingCardEq (n : ℕ) :
    2 * n + 1 = 2 * (Finset.univ : Finset (Fin n)).card + 1 := by
  simp

private theorem pairingCast_vertexGraph_reachable_iff
    {m n : ℕ} (h : m = n) (pairing : Pairing m) {Vertex : Type*}
    (vertexOfLegM : Fin (2 * m) → Vertex)
    (vertexOfLegN : Fin (2 * n) → Vertex)
    (hvertex : ∀ p : Fin (2 * n),
      vertexOfLegM
          ((finCongr (congrArg (fun k : ℕ => 2 * k) h.symm)) p) =
        vertexOfLegN p)
    (v w : Vertex) :
    ((Equiv.cast (congrArg Pairing h) pairing).vertexGraph vertexOfLegN).Reachable v w ↔
      (pairing.vertexGraph vertexOfLegM).Reachable v w := by
  subst n
  have hfun : vertexOfLegM = vertexOfLegN := by
    funext p
    simpa using hvertex p
  subst vertexOfLegN
  simp

/-- The actual two-point diagram on explicit `Fin S.card` slots obtained from one interaction order. -/
noncomputable def TwoPointDiagram.inInteractionOrder
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S) :
    TwoPointDiagram ExternalLabel InternalLabel S.card
      (Finset.univ : Finset (Fin S.card)) where
  externalLabel := d.externalLabel
  vertexLabel := fun v => d.vertexLabel (order v.1)
  pairing := Equiv.cast
    (congrArg Pairing (orderedTwoPointPairingCardEq S.card))
    (d.pairingInInteractionOrder order)

/-- Standard explicit vertex incidence agrees with the cardinality-normalized ordered incidence. -/
theorem TwoPointDiagram.inInteractionOrder_vertexGraph_reachable_iff
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S)
    (v w : TwoPointVertex (Finset.univ : Finset (Fin S.card))) :
    (d.inInteractionOrder order).vertexGraph.Reachable v w ↔
      d.vertexGraph.Reachable
        (twoPointInteractionOrderVertexEquiv order v)
        (twoPointInteractionOrderVertexEquiv order w) := by
  let h := orderedTwoPointPairingCardEq S.card
  have hvertex : ∀ p : Fin (2 * (2 * (Finset.univ : Finset (Fin S.card)).card + 1)),
      orderedTwoPointVertexOfLeg S.card
          ((finCongr (congrArg (fun k : ℕ => 2 * k) h.symm)) p) =
        twoPointVertexOfLeg p := by
    intro p
    unfold orderedTwoPointVertexOfLeg
    apply congrArg twoPointVertexOfLeg
    apply Fin.ext
    rfl
  rw [TwoPointDiagram.inInteractionOrder, TwoPointDiagram.vertexGraph]
  exact (pairingCast_vertexGraph_reachable_iff h
    (d.pairingInInteractionOrder order)
    (orderedTwoPointVertexOfLeg S.card) twoPointVertexOfLeg hvertex v w).trans
      (d.pairingInInteractionOrder_reachable_iff order v w)

/-- External connectedness is invariant under interaction-vertex ordering. -/
theorem TwoPointDiagram.inInteractionOrder_isExternallyConnected_iff
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S) :
    (d.inInteractionOrder order).IsExternallyConnected ↔ d.IsExternallyConnected := by
  rw [d.isExternallyConnected_iff_hasNoVacuumComponent,
    (d.inInteractionOrder order).isExternallyConnected_iff_hasNoVacuumComponent]
  constructor
  · intro h v
    let v' : ↥(Finset.univ : Finset (Fin S.card)) :=
      (finEquivUnivSubtype S.card) (order.symm v)
    obtain ⟨e, he⟩ := h v'
    refine ⟨e, ?_⟩
    have he' := ((d.inInteractionOrder_vertexGraph_reachable_iff order
      (Sum.inl e) (Sum.inr v')).1 he)
    simpa [twoPointInteractionOrderVertexEquiv, v'] using he'
  · intro h v
    obtain ⟨e, he⟩ := h (order v.1)
    refine ⟨e, ?_⟩
    apply (d.inInteractionOrder_vertexGraph_reachable_iff order
      (Sum.inl e) (Sum.inr v)).2
    have hv : (finEquivUnivSubtype S.card).symm v = v.1 := rfl
    simpa [twoPointInteractionOrderVertexEquiv, hv] using he

end Common
end SecondQuantization
