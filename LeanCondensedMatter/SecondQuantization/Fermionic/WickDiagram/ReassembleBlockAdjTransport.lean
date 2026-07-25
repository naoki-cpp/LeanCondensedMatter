import LeanCondensedMatter.SecondQuantization.Fermionic.WickDiagram.ReassembleComponentBlockSubset

set_option linter.style.header false

/-!
# Transporting adjacency/reachability from a block's own diagram into `reassemble`

The remaining half of `componentBlock (reassemble π F) v = π.part v` needs the converse inclusion
`π.part v ⊆ componentBlock (reassemble π F) v`, which in turn needs every vertex of a block `B` to
be reachable from any other **in the reassembled diagram**, using that `F B` is itself connected.
This file builds the bridge: `QuarticWickDiagram.reassembleVertex` includes a block's own vertices
back into `↥S` (via `Finpartition.equivSigmaParts.symm`), and adjacency/reachability in `F B`'s own
`vertexGraph` transports along it into `reassemble π F`'s `vertexGraph`.
-/

namespace SecondQuantization

variable {Mode : Type*} {N : ℕ}

/-- **A block `B`'s own vertex, included back into `↥S`**, via `Finpartition.equivSigmaParts`'s
inverse. -/
noncomputable def QuarticWickDiagram.reassembleVertex {S : Finset (Fin N)} (π : Finpartition S)
    (B : π.parts) (v : ↥(B : Finset (Fin N))) : ↥S :=
  π.equivSigmaParts.symm ⟨B, v⟩

/-- **`reassembleVertex` is injective** (for a fixed block `B`). -/
theorem QuarticWickDiagram.reassembleVertex_injective {S : Finset (Fin N)} (π : Finpartition S)
    (B : π.parts) : Function.Injective (QuarticWickDiagram.reassembleVertex π B) := by
  intro v w hvw
  have h2 : (⟨B, v⟩ : Σ t : π.parts, ↥(t : Finset (Fin N))) = ⟨B, w⟩ :=
    π.equivSigmaParts.symm.injective hvw
  simpa using h2

/-- **Adjacency in a block's own diagram transports into `reassemble`'s `vertexGraph`.** -/
theorem QuarticWickDiagram.reassemble_adj_of_adj_component {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N))) (B : π.parts)
    {u' w' : ↥(B : Finset (Fin N))} (h : (F B).1.vertexGraph.Adj u' w') :
    (QuarticWickDiagram.reassemble π F).vertexGraph.Adj (QuarticWickDiagram.reassembleVertex π B u')
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
          (Equiv.sigmaCongrRight fun B => (F B).1.pairing.partner) := rfl
    rw [hlhs, Equiv.permCongr_apply, Equiv.symm_symm, hbig]
    rfl
  have hw : vertexOfLeg ((QuarticWickDiagram.reassemble π F).pairing.partner leg) =
      QuarticWickDiagram.reassembleVertex π B w' := by
    rw [hpartner, QuarticWickDiagram.bigLegEquiv_symm_sigma_mk]
    rw [vertexOfLeg_legOfVertexLocal, hw']
    rfl
  exact ⟨fun h => hne' (QuarticWickDiagram.reassembleVertex_injective π B h), leg, hu, hw⟩

/-- **Reachability in a block's own diagram transports into `reassemble`'s `vertexGraph`.** -/
theorem QuarticWickDiagram.reassemble_reachable_of_reachable_component {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N))) (B : π.parts)
    {u' w' : ↥(B : Finset (Fin N))} (h : (F B).1.vertexGraph.Reachable u' w') :
    (QuarticWickDiagram.reassemble π F).vertexGraph.Reachable
      (QuarticWickDiagram.reassembleVertex π B u')
      (QuarticWickDiagram.reassembleVertex π B w') := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj _ ih =>
    exact (SimpleGraph.Adj.reachable
      (QuarticWickDiagram.reassemble_adj_of_adj_component π F B hadj)).trans ih

end SecondQuantization
