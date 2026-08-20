import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Diagram
import LeanCondensedMatter.Combinatorics.PerfectPairing.Relabel

set_option linter.style.header false

/-!
# Ordered labelled quartic diagrams

A vertex order identifies a finite diagram's vertices with slots `Fin S.card`. The induced leg
permutation transports the pairing to the slot enumeration, giving an equivalence between a labelled
quartic diagram and a slot-indexed label sequence together with a pairing.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {Label : Type*} {N : ℕ}

/-- A bijection between ordered slots and a finite vertex set. -/
abbrev QuarticVertexOrder (S : Finset (Fin N)) := Fin S.card ≃ ↥S

/-- A diagram's commutative vertex weight reindexed along a chosen vertex order. -/
theorem QuarticDiagram.vertexWeight_eq_prod_vertexLabel_order {M : Type*} [CommMonoid M]
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S) (w : Label → M)
    (order : QuarticVertexOrder S) :
    d.vertexWeight w = ∏ i : Fin S.card, w (d.vertexLabel (order i)) := by
  rw [QuarticDiagram.vertexWeight]
  exact (Equiv.prod_comp order (fun v => w (d.vertexLabel v))).symm

/-- The flattened-leg relabeling induced by a vertex order. -/
noncomputable def orderedLegToDiagramLeg (S : Finset (Fin N)) (order : QuarticVertexOrder S) :
    Equiv.Perm (Fin (2 * (2 * S.card))) :=
  (orderedQuarticLegEquiv S.card).trans
    ((order.prodCongr (Equiv.refl (Fin 4))).trans (quarticLegEquiv S).symm)

/-- Flattened quartic legs in distinct vertex-slot blocks are ordered exactly by their slots. -/
theorem orderedQuarticLegEquiv_symm_lt_symm_iff_fst_lt_of_ne
    (n : ℕ) (i j : Fin n) (a b : Fin 4) (hij : i ≠ j) :
    (orderedQuarticLegEquiv n).symm (i, a) <
        (orderedQuarticLegEquiv n).symm (j, b) ↔ i < j := by
  have hp' : ((orderedQuarticLegEquiv n).symm (i, a)).val = a.val + 4 * i.val := by
    simp [orderedQuarticLegEquiv, finProdFinEquiv]
  have hq' : ((orderedQuarticLegEquiv n).symm (j, b)).val = b.val + 4 * j.val := by
    simp [orderedQuarticLegEquiv, finProdFinEquiv]
  change ((orderedQuarticLegEquiv n).symm (i, a)).val <
      ((orderedQuarticLegEquiv n).symm (j, b)).val ↔ i.val < j.val
  rw [hp', hq']
  have ha : a.val < 4 := a.isLt
  have hb : b.val < 4 := b.isLt
  have hij' : i.val ≠ j.val := by
    intro h
    exact hij (Fin.ext h)
  omega

/-- Flattened quartic legs in the same vertex-slot block are ordered by their local leg indices. -/
theorem orderedQuarticLegEquiv_symm_lt_symm_iff_snd_lt_of_fst_eq
    (n : ℕ) (p q : Fin n × Fin 4) (h : p.1 = q.1) :
    (orderedQuarticLegEquiv n).symm p <
        (orderedQuarticLegEquiv n).symm q ↔ p.2 < q.2 := by
  rcases p with ⟨i, a⟩
  rcases q with ⟨j, b⟩
  change i = j at h
  subst j
  have hp' : ((orderedQuarticLegEquiv n).symm (i, a)).val = a.val + 4 * i.val := by
    simp [orderedQuarticLegEquiv, finProdFinEquiv]
  have hq' : ((orderedQuarticLegEquiv n).symm (i, b)).val = b.val + 4 * i.val := by
    simp [orderedQuarticLegEquiv, finProdFinEquiv]
  change ((orderedQuarticLegEquiv n).symm (i, a)).val <
      ((orderedQuarticLegEquiv n).symm (i, b)).val ↔ a.val < b.val
  rw [hp', hq']
  omega

/-- A diagram's pairing transported to a vertex order's slot enumeration. -/
noncomputable def QuarticDiagram.pairingInOrder {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (order : QuarticVertexOrder S) :
    Combinatorics.Pairing (2 * S.card) :=
  d.pairing.relabel (orderedLegToDiagramLeg S order)

/-- Slot-indexed labels together with a pairing in the same slot enumeration. -/
abbrev OrderedQuarticDiagramData (Label : Type*) (n : ℕ) :=
  (Fin n → Label) × Combinatorics.Pairing (2 * n)

/-- A labelled quartic diagram is equivalent to ordered data for any fixed vertex order. -/
noncomputable def quarticDiagramEquivOrderedData {S : Finset (Fin N)}
    (order : QuarticVertexOrder S) :
    QuarticDiagram Label N S ≃ OrderedQuarticDiagramData Label S.card where
  toFun d := (fun i => d.vertexLabel (order i), d.pairingInOrder order)
  invFun x :=
    { vertexLabel := fun v => x.1 (order.symm v)
      pairing := x.2.relabel (orderedLegToDiagramLeg S order).symm }
  left_inv d := by
    apply QuarticDiagram.ext
    · funext v
      simp
    · simp [QuarticDiagram.pairingInOrder]
  right_inv x := by
    obtain ⟨labels, pairing⟩ := x
    refine Prod.ext ?_ ?_
    · funext i
      simp
    · simp [QuarticDiagram.pairingInOrder]

/-- Reindex a finite sum over labelled diagrams as a sum over ordered data. -/
theorem sum_quarticDiagram_eq_sum_orderedData [Fintype Label] {S : Finset (Fin N)}
    (order : QuarticVertexOrder S) (F : OrderedQuarticDiagramData Label S.card → ℂ) :
    ∑ d : QuarticDiagram Label N S, F (quarticDiagramEquivOrderedData order d) =
      ∑ x : OrderedQuarticDiagramData Label S.card, F x :=
  Equiv.sum_comp (quarticDiagramEquivOrderedData order) F

/-- A vertex order exists for every finite vertex set. -/
noncomputable def someVertexOrder (S : Finset (Fin N)) : QuarticVertexOrder S :=
  ((Fintype.equivFin (↥S)).trans (finCongr (Fintype.card_coe S))).symm

/-- The number of vertex orders is `S.card!`. -/
theorem card_quarticVertexOrder (S : Finset (Fin N)) :
    Fintype.card (QuarticVertexOrder S) = S.card.factorial := by
  rw [Fintype.card_equiv (someVertexOrder S), Fintype.card_fin]

end Common
end SecondQuantization
