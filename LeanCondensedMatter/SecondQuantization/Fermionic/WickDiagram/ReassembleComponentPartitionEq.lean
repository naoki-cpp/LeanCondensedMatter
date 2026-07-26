import LeanCondensedMatter.SecondQuantization.Fermionic.WickDiagram.ReassembleDecompose

set_option linter.style.header false

/-!
# Component partition of a reassembled quartic Wick diagram

The connected components of `QuarticWickDiagram.reassemble π F` are exactly the blocks of `π`.
The proof has two graph-theoretic directions: reassembled edges stay inside one block, while each
connected block diagram `F B` embeds back into the reassembled graph.
-/

namespace SecondQuantization

variable {Mode : Type*} {N : ℕ}

/-- A vertex of a block `B`, included back into the ambient vertex set. -/
noncomputable def QuarticWickDiagram.reassembleVertex {S : Finset (Fin N)} (π : Finpartition S)
    (B : π.parts) (v : ↥(B : Finset (Fin N))) : ↥S :=
  π.equivSigmaParts.symm ⟨B, v⟩

private theorem QuarticWickDiagram.reassembleVertex_injective {S : Finset (Fin N)}
    (π : Finpartition S) (B : π.parts) :
    Function.Injective (QuarticWickDiagram.reassembleVertex π B) := by
  intro v w hvw
  have h : (⟨B, v⟩ : Σ t : π.parts, ↥(t : Finset (Fin N))) = ⟨B, w⟩ :=
    π.equivSigmaParts.symm.injective hvw
  simpa using h

private theorem QuarticWickDiagram.bigLegEquiv_fst_eq_part {S : Finset (Fin N)}
    (π : Finpartition S) (leg : Fin (2 * (2 * S.card))) :
    ((QuarticWickDiagram.bigLegEquiv π leg).1 : Finset (Fin N)) =
      π.part (vertexOfLeg leg : Fin N) := by
  conv_lhs => rw [← QuarticWickDiagram.legOfVertexLocal_vertexOfLeg_localLegOfLeg leg]
  rw [QuarticWickDiagram.bigLegEquiv_legOfVertexLocal]
  rfl

private theorem QuarticWickDiagram.reassemble_partner_bigLegEquiv_fst {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N)))
    (leg : Fin (2 * (2 * S.card))) :
    (QuarticWickDiagram.bigLegEquiv π
        ((QuarticWickDiagram.reassemble π F).pairing.partner leg)).1 =
      (QuarticWickDiagram.bigLegEquiv π leg).1 := by
  have hlhs : (QuarticWickDiagram.reassemble π F).pairing.partner =
      (QuarticWickDiagram.bigLegEquiv π).symm.permCongr
        (Equiv.sigmaCongrRight fun B => (F B).1.pairing.partner) := rfl
  rw [hlhs, Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  rfl

private theorem QuarticWickDiagram.reassemble_vertexGraph_adj_same_part
    {S : Finset (Fin N)} (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N)))
    {u w : ↥S} (h : (QuarticWickDiagram.reassemble π F).vertexGraph.Adj u w) :
    π.part (u : Fin N) = π.part (w : Fin N) := by
  obtain ⟨-, leg, hu, hw⟩ := h
  rw [← hu, ← hw, ← QuarticWickDiagram.bigLegEquiv_fst_eq_part,
    ← QuarticWickDiagram.bigLegEquiv_fst_eq_part,
    QuarticWickDiagram.reassemble_partner_bigLegEquiv_fst]

private theorem QuarticWickDiagram.reassemble_reachable_same_part {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N)))
    {u w : ↥S} (h : (QuarticWickDiagram.reassemble π F).vertexGraph.Reachable u w) :
    π.part (u : Fin N) = π.part (w : Fin N) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons hadj _ ih =>
    exact (QuarticWickDiagram.reassemble_vertexGraph_adj_same_part π F hadj).trans ih

private theorem QuarticWickDiagram.reassemble_componentBlock_subset_part
    {S : Finset (Fin N)} (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N)))
    (v : ↥S) :
    (QuarticWickDiagram.reassemble π F).componentBlock v ⊆ π.part (v : Fin N) := by
  intro x hx
  rw [QuarticWickDiagram.mem_componentBlock] at hx
  obtain ⟨hxS, hreach⟩ := hx
  rw [← QuarticWickDiagram.reassemble_reachable_same_part π F hreach]
  exact π.mem_part hxS

private theorem QuarticWickDiagram.reassemble_adj_of_adj_component {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N)))
    (B : π.parts) {u' w' : ↥(B : Finset (Fin N))} (h : (F B).1.vertexGraph.Adj u' w') :
    (QuarticWickDiagram.reassemble π F).vertexGraph.Adj
      (QuarticWickDiagram.reassembleVertex π B u')
      (QuarticWickDiagram.reassembleVertex π B w') := by
  obtain ⟨hne', leg', hu', hw'⟩ := h
  set leg := (QuarticWickDiagram.bigLegEquiv π).symm ⟨B, leg'⟩ with hlegdef
  have hbig : QuarticWickDiagram.bigLegEquiv π leg = ⟨B, leg'⟩ :=
    Equiv.apply_symm_apply _ _
  have hu : vertexOfLeg leg = QuarticWickDiagram.reassembleVertex π B u' := by
    rw [hlegdef, QuarticWickDiagram.bigLegEquiv_symm_sigma_mk]
    rw [vertexOfLeg_legOfVertexLocal, hu']
    rfl
  have hpartner :
      (QuarticWickDiagram.reassemble π F).pairing.partner leg =
        (QuarticWickDiagram.bigLegEquiv π).symm ⟨B, (F B).1.pairing.partner leg'⟩ := by
    have hlhs : (QuarticWickDiagram.reassemble π F).pairing.partner =
        (QuarticWickDiagram.bigLegEquiv π).symm.permCongr
          (Equiv.sigmaCongrRight fun C => (F C).1.pairing.partner) := rfl
    rw [hlhs, Equiv.permCongr_apply, Equiv.symm_symm, hbig]
    rfl
  have hw : vertexOfLeg ((QuarticWickDiagram.reassemble π F).pairing.partner leg) =
      QuarticWickDiagram.reassembleVertex π B w' := by
    rw [hpartner, QuarticWickDiagram.bigLegEquiv_symm_sigma_mk]
    rw [vertexOfLeg_legOfVertexLocal, hw']
    rfl
  exact ⟨fun hEq => hne' (QuarticWickDiagram.reassembleVertex_injective π B hEq),
    leg, hu, hw⟩

private theorem QuarticWickDiagram.reassemble_reachable_of_reachable_component
    {S : Finset (Fin N)} (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N)))
    (B : π.parts) {u' w' : ↥(B : Finset (Fin N))}
    (h : (F B).1.vertexGraph.Reachable u' w') :
    (QuarticWickDiagram.reassemble π F).vertexGraph.Reachable
      (QuarticWickDiagram.reassembleVertex π B u')
      (QuarticWickDiagram.reassembleVertex π B w') := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj _ ih =>
    exact (SimpleGraph.Adj.reachable
      (QuarticWickDiagram.reassemble_adj_of_adj_component π F B hadj)).trans ih

private theorem QuarticWickDiagram.part_subset_reassemble_componentBlock
    {S : Finset (Fin N)} (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N)))
    (v : ↥S) :
    π.part (v : Fin N) ⊆ (QuarticWickDiagram.reassemble π F).componentBlock v := by
  intro x hx
  set B := (π.equivSigmaParts v).1
  have hxB : x ∈ (B : Finset (Fin N)) := hx
  have hxS : x ∈ S := π.le B.2 hxB
  have hreach0 : (F B).1.vertexGraph.Reachable (⟨x, hxB⟩ : ↥(B : Finset (Fin N)))
      (π.equivSigmaParts v).2 :=
    (F B).2.1 ⟨x, hxB⟩ (π.equivSigmaParts v).2
  have hreach := QuarticWickDiagram.reassemble_reachable_of_reachable_component π F B hreach0
  have heq1 : QuarticWickDiagram.reassembleVertex π B ⟨x, hxB⟩ = (⟨x, hxS⟩ : ↥S) := rfl
  have heq2 : QuarticWickDiagram.reassembleVertex π B (π.equivSigmaParts v).2 = v := by
    change π.equivSigmaParts.symm ⟨B, (π.equivSigmaParts v).2⟩ = v
    exact π.equivSigmaParts.symm_apply_apply v
  rw [heq1, heq2] at hreach
  exact (QuarticWickDiagram.mem_componentBlock (QuarticWickDiagram.reassemble π F) v).2
    ⟨hxS, hreach⟩

private theorem QuarticWickDiagram.reassemble_componentBlock_eq_part
    {S : Finset (Fin N)} (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N)))
    (v : ↥S) :
    (QuarticWickDiagram.reassemble π F).componentBlock v = π.part (v : Fin N) :=
  Finset.Subset.antisymm (QuarticWickDiagram.reassemble_componentBlock_subset_part π F v)
    (QuarticWickDiagram.part_subset_reassemble_componentBlock π F v)

/-- The component partition of a reassembled family is the original partition. -/
theorem QuarticWickDiagram.componentPartition_reassemble {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N))) :
    (QuarticWickDiagram.reassemble π F).componentPartition = π := by
  apply Finpartition.ext
  apply Finset.Subset.antisymm
  · intro B hB
    obtain ⟨v, rfl⟩ := (QuarticWickDiagram.reassemble π F).exists_componentBlock_eq_of_mem hB
    rw [QuarticWickDiagram.reassemble_componentBlock_eq_part]
    exact π.part_mem.2 v.2
  · intro B hB
    obtain ⟨v, hv⟩ := π.nonempty_of_mem_parts hB
    have hvS : v ∈ S := π.le hB hv
    have hpart : π.part v = B := π.part_eq_of_mem hB hv
    have hmem :=
      (QuarticWickDiagram.reassemble π F).componentBlock_mem_componentPartition (⟨v, hvS⟩ : ↥S)
    rwa [QuarticWickDiagram.reassemble_componentBlock_eq_part, hpart] at hmem

end SecondQuantization
