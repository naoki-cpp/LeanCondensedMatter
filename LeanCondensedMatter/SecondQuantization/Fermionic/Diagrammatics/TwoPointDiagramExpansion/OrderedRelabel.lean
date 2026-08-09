import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.InteractionVertexRelabelCovariance
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.OrderedAmplitude

set_option linter.style.header false

/-!
# Interaction relabeling between two vertex orders

Two explicit presentations of the same finite-set fixed-external diagram differ only by the
interaction-slot permutation carrying the second vertex order to the first. This lets the LCT use
the already proved injective-time/integrated relabel covariance when the global vertex-order sum is
reindexed by component-local orders and a component shuffle.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {N : ℕ}

omit [LinearOrder Mode] [Fintype Mode] in
/-- Cast the flattened explicit `4n+2` position type to the `Finset.univ.card` presentation used by
the stored fixed-external pairing. -/
def explicitTwoPointPositionCast (n : ℕ) :
    Fin (2 * (2 * n + 1)) ≃
      Fin (2 * (2 * (Finset.univ : Finset (Fin n)).card + 1)) :=
  finCongr (by simp)

omit [LinearOrder Mode] [Fintype Mode] in
/-- The exact-`Fin n` version of the flattened interaction-slot permutation. -/
noncomputable def interactionVertexPositionRelabelFin {n : ℕ} (π : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (2 * (2 * n + 1))) :=
  (explicitTwoPointPositionCast n).trans <|
    (interactionVertexPositionRelabel π).trans (explicitTwoPointPositionCast n).symm

omit [LinearOrder Mode] [Fintype Mode] in
@[simp]
theorem explicitTwoPointPositionCast_interactionVertexPositionRelabelFin
    {n : ℕ} (π : Equiv.Perm (Fin n)) (p : Fin (2 * (2 * n + 1))) :
    explicitTwoPointPositionCast n (interactionVertexPositionRelabelFin π p) =
      interactionVertexPositionRelabel π (explicitTwoPointPositionCast n p) := by
  change explicitTwoPointPositionCast n
      ((explicitTwoPointPositionCast n).symm
        (interactionVertexPositionRelabel π (explicitTwoPointPositionCast n p))) = _
  exact (explicitTwoPointPositionCast n).apply_symm_apply _

omit [LinearOrder Mode] [Fintype Mode] in
@[simp]
theorem explicitTwoPointPositionCast_interactionVertexPositionRelabelFin_symm
    {n : ℕ} (π : Equiv.Perm (Fin n)) (p : Fin (2 * (2 * n + 1))) :
    explicitTwoPointPositionCast n ((interactionVertexPositionRelabelFin π).symm p) =
      (interactionVertexPositionRelabel π).symm (explicitTwoPointPositionCast n p) := by
  apply (interactionVertexPositionRelabel π).injective
  rw [(interactionVertexPositionRelabel π).apply_symm_apply]
  rw [← explicitTwoPointPositionCast_interactionVertexPositionRelabelFin
    π ((interactionVertexPositionRelabelFin π).symm p)]
  simp

omit [LinearOrder Mode] [Fintype Mode] in
private theorem pairingCast_partner {m n : ℕ} (h : m = n)
    (pairing : Pairing m) (p : Fin (2 * n)) :
    (finCongr (congrArg (fun k : ℕ => 2 * k) h.symm))
        ((Equiv.cast (congrArg Pairing h) pairing).partner p) =
      pairing.partner
        ((finCongr (congrArg (fun k : ℕ => 2 * k) h.symm)) p) := by
  subst n
  rfl

omit [LinearOrder Mode] [Fintype Mode] in
/-- The explicit position cast intertwines partners before and after the standard fixed-diagram
pairing-cardinality cast. -/
theorem explicitTwoPointPositionCast_orderedTwoPointPairingCastEquiv_partner
    {n : ℕ} (pairing : Pairing (2 * (Finset.univ : Finset (Fin n)).card + 1))
    (p : Fin (2 * (2 * n + 1))) :
    explicitTwoPointPositionCast n
        ((orderedTwoPointPairingCastEquiv n pairing).partner p) =
      pairing.partner (explicitTwoPointPositionCast n p) := by
  let h : 2 * (Finset.univ : Finset (Fin n)).card + 1 = 2 * n + 1 := by simp
  have hcast : orderedTwoPointPairingCastEquiv n =
      Equiv.cast (congrArg Pairing h) := by
    unfold orderedTwoPointPairingCastEquiv
    congr
  have hc : explicitTwoPointPositionCast n =
      finCongr (congrArg (fun k : ℕ => 2 * k) h.symm) := by
    apply Equiv.ext
    intro x
    rfl
  rw [hcast, hc]
  exact pairingCast_partner h pairing p

omit [LinearOrder Mode] [Fintype Mode] in
/-- Casting the stored fixed-external pairing to exact `Fin n` slots commutes with interaction-slot
relabeling after conjugating the flattened position permutation by the same cardinality cast. -/
theorem orderedTwoPointPairingCastEquiv_relabelInteractionVertices
    {n : ℕ} (pairing : Pairing (2 * (Finset.univ : Finset (Fin n)).card + 1))
    (π : Equiv.Perm (Fin n)) :
    orderedTwoPointPairingCastEquiv n
        (pairing.relabel (interactionVertexPositionRelabel π)) =
      (orderedTwoPointPairingCastEquiv n pairing).relabel
        (interactionVertexPositionRelabelFin π) := by
  apply Pairing.ext
  apply Equiv.ext
  intro p
  apply (explicitTwoPointPositionCast n).injective
  calc
    explicitTwoPointPositionCast n
        ((orderedTwoPointPairingCastEquiv n
          (pairing.relabel (interactionVertexPositionRelabel π))).partner p) =
      (pairing.relabel (interactionVertexPositionRelabel π)).partner
        (explicitTwoPointPositionCast n p) :=
      explicitTwoPointPositionCast_orderedTwoPointPairingCastEquiv_partner _ _
    _ = (interactionVertexPositionRelabel π).symm
        (pairing.partner
          (interactionVertexPositionRelabel π (explicitTwoPointPositionCast n p))) := by
      rw [Pairing.relabel_partner]
    _ = (interactionVertexPositionRelabel π).symm
        (pairing.partner
          (explicitTwoPointPositionCast n (interactionVertexPositionRelabelFin π p))) := by
      rw [explicitTwoPointPositionCast_interactionVertexPositionRelabelFin]
    _ = (interactionVertexPositionRelabel π).symm
        (explicitTwoPointPositionCast n
          ((orderedTwoPointPairingCastEquiv n pairing).partner
            (interactionVertexPositionRelabelFin π p))) := by
      rw [explicitTwoPointPositionCast_orderedTwoPointPairingCastEquiv_partner]
    _ = explicitTwoPointPositionCast n
        ((interactionVertexPositionRelabelFin π).symm
          ((orderedTwoPointPairingCastEquiv n pairing).partner
            (interactionVertexPositionRelabelFin π p))) := by
      symm
      exact explicitTwoPointPositionCast_interactionVertexPositionRelabelFin_symm _ _
    _ = explicitTwoPointPositionCast n
        (((orderedTwoPointPairingCastEquiv n pairing).relabel
          (interactionVertexPositionRelabelFin π)).partner p) := by
      rw [Pairing.relabel_partner]

omit [LinearOrder Mode] [Fintype Mode] in
/-- The exact-slot interaction relabel taking the second ordered presentation to the first, followed
by the first ordered-to-ambient leg map, is the second ordered-to-ambient leg map. -/
theorem interactionVertexPositionRelabelFin_orderChange
    {S : Finset (Fin N)} (order₁ order₂ : Common.QuarticVertexOrder S) :
    (interactionVertexPositionRelabelFin (order₂.trans order₁.symm)).trans
        (Common.orderedTwoPointLegToDiagramLeg order₁) =
      Common.orderedTwoPointLegToDiagramLeg order₂ := by
  apply Equiv.ext
  intro p
  let π : Equiv.Perm (Fin S.card) := order₂.trans order₁.symm
  unfold Common.orderedTwoPointLegToDiagramLeg
  simp only [Equiv.trans_apply]
  apply (Common.twoPointLegEquiv S).injective
  simp only [Equiv.apply_symm_apply]
  have hc :
      (finCongr (by simp) :
        Fin (2 * (2 * S.card + 1)) ≃
          Fin (2 * (2 * (Finset.univ : Finset (Fin S.card)).card + 1))) =
        explicitTwoPointPositionCast S.card := by
    rfl
  rw [hc]
  rw [explicitTwoPointPositionCast_interactionVertexPositionRelabelFin]
  rw [twoPointLegEquiv_interactionVertexPositionRelabel]
  generalize
      Common.twoPointLegEquiv (Finset.univ : Finset (Fin S.card))
        (explicitTwoPointPositionCast S.card p) = leg
  rcases leg with e | ⟨v, l⟩ <;>
    simp [interactionVertexLegRelabel, Common.twoPointInteractionOrderLegEquiv,
      Common.orderedTwoPointLegDataEquivUniv, Common.finEquivUnivSubtype]

omit [LinearOrder Mode] [Fintype Mode] in
/-- Reindexing the same arbitrary-set fixed-external diagram by two interaction orders gives explicit
diagrams related by the corresponding interaction-slot permutation. -/
theorem fixedExternalTwoPointWickDiagramOrderEquiv_relabel_orderChange
    {S : Finset (Fin N)} (i j : Mode)
    (d : FixedExternalTwoPointWickDiagramOn Mode N S i j)
    (order₁ order₂ : Common.QuarticVertexOrder S) :
    (fixedExternalTwoPointWickDiagramOrderEquiv i j order₁ d).relabelInteractionVertices
        (order₂.trans order₁.symm) =
      fixedExternalTwoPointWickDiagramOrderEquiv i j order₂ d := by
  apply Subtype.ext
  apply Common.TwoPointDiagram.ext
  · rfl
  · funext v
    change d.1.vertexLabel (order₁ ((order₂.trans order₁.symm) v.1)) =
      d.1.vertexLabel (order₂ v.1)
    simp
  · change
      (((orderedTwoPointPairingCastEquiv S.card).symm
        (d.1.pairingInInteractionOrder order₁)).relabel
          (interactionVertexPositionRelabel (order₂.trans order₁.symm))) =
        (orderedTwoPointPairingCastEquiv S.card).symm
          (d.1.pairingInInteractionOrder order₂)
    apply (orderedTwoPointPairingCastEquiv S.card).injective
    rw [orderedTwoPointPairingCastEquiv_relabelInteractionVertices]
    rw [(orderedTwoPointPairingCastEquiv S.card).apply_symm_apply]
    rw [(orderedTwoPointPairingCastEquiv S.card).apply_symm_apply]
    unfold Common.TwoPointDiagram.pairingInInteractionOrder
    rw [Pairing.relabel_trans]
    rw [interactionVertexPositionRelabelFin_orderChange]

end Fermionic
end SecondQuantization
