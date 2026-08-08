import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ExternalVacuumReassemble

set_option linter.style.header false

/-!
# Structural laws for external/vacuum reassembly

The reassembled pairing never crosses the external/vacuum split.  The external core therefore maps
into the ambient external component, while the complementary quartic diagram remains unreachable
from the external vertices.  These facts identify the interaction support of the ambient external
component exactly with the chosen external subset.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

private theorem externalVertexEmbed_injective {S E : Finset (Fin N)} (hE : E ⊆ S) :
    Function.Injective (TwoPointDiagram.externalVertexEmbed hE) := by
  intro v w h
  rcases v with e | v <;> rcases w with e' | w <;>
    simp_all [TwoPointDiagram.externalVertexEmbed]
  exact Subtype.ext (Sum.inr.inj h)

/-- Adjacency inside the connected external core is preserved by reassembly. -/
theorem TwoPointDiagram.reassembleExternalVacuum_external_adj
    {S E : Finset (Fin N)} (hE : E ⊆ S)
    (external : ExternallyConnectedTwoPointDiagram ExternalLabel InternalLabel N E)
    (vacuum : QuarticDiagram InternalLabel N (S \ E))
    {v w : TwoPointVertex E}
    (hvw : external.1.vertexGraph.Adj v w) :
    (TwoPointDiagram.reassembleExternalVacuum hE external vacuum).vertexGraph.Adj
      (TwoPointDiagram.externalVertexEmbed hE v)
      (TwoPointDiagram.externalVertexEmbed hE w) := by
  rcases hvw with ⟨hne, leg, hv, hw⟩
  refine ⟨externalVertexEmbed_injective hE hne,
    (TwoPointDiagram.externalVacuumLegEquiv hE).symm (Sum.inl leg), ?_, ?_⟩
  · rw [TwoPointDiagram.vertexOfLeg_externalVacuumLegEquiv_symm_external]
    exact congrArg (TwoPointDiagram.externalVertexEmbed hE) hv
  · rw [TwoPointDiagram.reassembleExternalVacuum_partner_external,
      TwoPointDiagram.vertexOfLeg_externalVacuumLegEquiv_symm_external]
    exact congrArg (TwoPointDiagram.externalVertexEmbed hE) hw

/-- Reachability inside the external core is preserved by reassembly. -/
theorem TwoPointDiagram.reassembleExternalVacuum_external_reachable
    {S E : Finset (Fin N)} (hE : E ⊆ S)
    (external : ExternallyConnectedTwoPointDiagram ExternalLabel InternalLabel N E)
    (vacuum : QuarticDiagram InternalLabel N (S \ E))
    {v w : TwoPointVertex E}
    (hvw : external.1.vertexGraph.Reachable v w) :
    (TwoPointDiagram.reassembleExternalVacuum hE external vacuum).vertexGraph.Reachable
      (TwoPointDiagram.externalVertexEmbed hE v)
      (TwoPointDiagram.externalVertexEmbed hE w) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hvw ⊢
  induction hvw with
  | refl => exact Relation.ReflTransGen.refl
  | tail hxy hyz ih =>
      exact Relation.ReflTransGen.tail ih
        (TwoPointDiagram.reassembleExternalVacuum_external_adj hE external vacuum hyz)

/-- An ambient vertex lies on the external side of a chosen interaction split. -/
def TwoPointDiagram.VertexInExternalPart {S E : Finset (Fin N)}
    (v : TwoPointVertex S) : Prop :=
  match v with
  | Sum.inl _ => True
  | Sum.inr w => w.1 ∈ E

@[simp]
theorem TwoPointDiagram.vertexInExternalPart_externalEmbed
    {S E : Finset (Fin N)} (hE : E ⊆ S) (v : TwoPointVertex E) :
    TwoPointDiagram.VertexInExternalPart
      (TwoPointDiagram.externalVertexEmbed hE v) := by
  rcases v with e | v
  · trivial
  · exact v.2

@[simp]
theorem TwoPointDiagram.not_vertexInExternalPart_vacuumEmbed
    {S E : Finset (Fin N)} (hE : E ⊆ S) (v : ↥(S \ E)) :
    ¬ TwoPointDiagram.VertexInExternalPart
      (TwoPointDiagram.vacuumVertexEmbed hE v) := by
  exact (Finset.mem_sdiff.mp v.2).2

/-- Pairing partners in a reassembled diagram lie on the same side of the external/vacuum split. -/
theorem TwoPointDiagram.reassembleExternalVacuum_partner_preserves_externalPart
    {S E : Finset (Fin N)} (hE : E ⊆ S)
    (external : ExternallyConnectedTwoPointDiagram ExternalLabel InternalLabel N E)
    (vacuum : QuarticDiagram InternalLabel N (S \ E))
    (leg : Fin (2 * (2 * S.card + 1))) :
    TwoPointDiagram.VertexInExternalPart (E := E) (twoPointVertexOfLeg leg) ↔
      TwoPointDiagram.VertexInExternalPart (E := E)
        (twoPointVertexOfLeg
          ((TwoPointDiagram.reassembleExternalVacuum hE external vacuum).pairing.partner leg)) := by
  let split := TwoPointDiagram.externalVacuumLegEquiv hE
  cases hsplit : split leg with
  | inl a =>
      have hleg : leg = split.symm (Sum.inl a) := by
        rw [← hsplit]
        exact split.symm_apply_apply leg
      subst leg
      rw [TwoPointDiagram.reassembleExternalVacuum_partner_external,
        TwoPointDiagram.vertexOfLeg_externalVacuumLegEquiv_symm_external,
        TwoPointDiagram.vertexOfLeg_externalVacuumLegEquiv_symm_external]
      simp
  | inr a =>
      have hleg : leg = split.symm (Sum.inr a) := by
        rw [← hsplit]
        exact split.symm_apply_apply leg
      subst leg
      rw [TwoPointDiagram.reassembleExternalVacuum_partner_vacuum,
        TwoPointDiagram.vertexOfLeg_externalVacuumLegEquiv_symm_vacuum,
        TwoPointDiagram.vertexOfLeg_externalVacuumLegEquiv_symm_vacuum]
      simp

/-- Every ambient edge of a reassembled diagram stays entirely on one side of the
external/vacuum split. -/
theorem TwoPointDiagram.reassembleExternalVacuum_adj_preserves_externalPart
    {S E : Finset (Fin N)} (hE : E ⊆ S)
    (external : ExternallyConnectedTwoPointDiagram ExternalLabel InternalLabel N E)
    (vacuum : QuarticDiagram InternalLabel N (S \ E))
    {v w : TwoPointVertex S}
    (hvw : (TwoPointDiagram.reassembleExternalVacuum hE external vacuum).vertexGraph.Adj v w) :
    TwoPointDiagram.VertexInExternalPart (E := E) v ↔
      TwoPointDiagram.VertexInExternalPart (E := E) w := by
  rcases hvw with ⟨_, leg, hv, hw⟩
  rw [← hv, ← hw]
  exact TwoPointDiagram.reassembleExternalVacuum_partner_preserves_externalPart
    hE external vacuum leg

/-- Reachability in a reassembled diagram preserves the external/vacuum side. -/
theorem TwoPointDiagram.reassembleExternalVacuum_reachable_preserves_externalPart
    {S E : Finset (Fin N)} (hE : E ⊆ S)
    (external : ExternallyConnectedTwoPointDiagram ExternalLabel InternalLabel N E)
    (vacuum : QuarticDiagram InternalLabel N (S \ E))
    {v w : TwoPointVertex S}
    (hvw : (TwoPointDiagram.reassembleExternalVacuum hE external vacuum).vertexGraph.Reachable v w) :
    TwoPointDiagram.VertexInExternalPart (E := E) v ↔
      TwoPointDiagram.VertexInExternalPart (E := E) w := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hvw
  induction hvw with
  | refl => rfl
  | tail hxy hyz ih =>
      exact ih.trans
        (TwoPointDiagram.reassembleExternalVacuum_adj_preserves_externalPart
          hE external vacuum hyz)

/-- Every interaction vertex of an externally connected two-point diagram is reachable from
external vertex `0`. -/
theorem TwoPointDiagram.reachable_zero_of_isExternallyConnected
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (hconn : d.IsExternallyConnected) (v : ↥S) :
    d.vertexGraph.Reachable (Sum.inl (0 : Fin 2)) (Sum.inr v) := by
  obtain ⟨e, hev⟩ := hconn.1 v
  have h0e : d.vertexGraph.Reachable
      (Sum.inl (0 : Fin 2)) (Sum.inl e) := by
    fin_cases e
    · exact SimpleGraph.Reachable.refl _
    · exact hconn.2
  exact h0e.trans hev

/-- The ambient external component of a reassembled diagram contains exactly the chosen interaction
subset `E`. -/
theorem TwoPointDiagram.interactionPart_externalComponent_reassembleExternalVacuum
    {S E : Finset (Fin N)} (hE : E ⊆ S)
    (external : ExternallyConnectedTwoPointDiagram ExternalLabel InternalLabel N E)
    (vacuum : QuarticDiagram InternalLabel N (S \ E)) :
    TwoPointDiagram.interactionPart
        ((TwoPointDiagram.reassembleExternalVacuum hE external vacuum).externalComponent 0) = E := by
  ext v
  rw [TwoPointDiagram.mem_interactionPart]
  constructor
  · rintro ⟨hvS, hvcomp⟩
    have hreach :
        (TwoPointDiagram.reassembleExternalVacuum hE external vacuum).vertexGraph.Reachable
          (Sum.inl (0 : Fin 2)) (Sum.inr ⟨v, hvS⟩) := by
      exact ((TwoPointDiagram.reassembleExternalVacuum hE external vacuum).mem_componentBlock
        (Sum.inl (0 : Fin 2)) (Sum.inr ⟨v, hvS⟩)).1 hvcomp |>.symm
    have hside :=
      (TwoPointDiagram.reassembleExternalVacuum_reachable_preserves_externalPart
        hE external vacuum hreach).mp trivial
    exact hside
  · intro hvE
    let w : ↥E := ⟨v, hvE⟩
    have hlocal := TwoPointDiagram.reachable_zero_of_isExternallyConnected
      external.1 external.2 w
    have hambient := TwoPointDiagram.reassembleExternalVacuum_external_reachable
      hE external vacuum hlocal
    refine ⟨hE hvE, ?_⟩
    apply ((TwoPointDiagram.reassembleExternalVacuum hE external vacuum).mem_componentBlock
      (Sum.inl (0 : Fin 2)) (Sum.inr ⟨v, hE hvE⟩)).2
    simpa [TwoPointDiagram.externalVertexEmbed] using hambient.symm

end Common
end SecondQuantization
