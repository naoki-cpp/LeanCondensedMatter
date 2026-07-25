import LeanCondensedMatter.SecondQuantization.Fermionic.WickDiagram.ReassembleAdjSamePart

set_option linter.style.header false

/-!
# `reassemble π F`'s component blocks stay inside `π`'s own blocks

The first (easier) half of `componentBlock (reassemble π F) v = π.part v` — the other half needs
each block's own connectedness (from `F`) and is deferred. Reachability in `vertexGraph` is
transitive same-part-ness by `reassemble_vertexGraph_adj_same_part`, applied along each edge of a
`SimpleGraph.Walk`.
-/

namespace SecondQuantization

variable {Mode : Type*} {N : ℕ}

/-- **Reachable vertices of `reassemble π F` lie in the same `π`-block.** -/
theorem QuarticWickDiagram.reassemble_reachable_same_part {S : Finset (Fin N)} (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N))) {u w : ↥S}
    (h : (QuarticWickDiagram.reassemble π F).vertexGraph.Reachable u w) :
    π.part (u : Fin N) = π.part (w : Fin N) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons hadj _ ih =>
    exact (QuarticWickDiagram.reassemble_vertexGraph_adj_same_part π F hadj).trans ih

/-- **`reassemble π F`'s component block at `v` stays inside `v`'s own `π`-block.** -/
theorem QuarticWickDiagram.reassemble_componentBlock_subset_part {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N)))
    (v : ↥S) :
    (QuarticWickDiagram.reassemble π F).componentBlock v ⊆ π.part (v : Fin N) := by
  intro x hx
  rw [QuarticWickDiagram.mem_componentBlock] at hx
  obtain ⟨hxS, hreach⟩ := hx
  rw [← QuarticWickDiagram.reassemble_reachable_same_part π F hreach]
  exact π.mem_part hxS

end SecondQuantization
