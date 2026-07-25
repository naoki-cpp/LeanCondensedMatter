import LeanCondensedMatter.SecondQuantization.Fermionic.WickDiagram.ReassembleBlockAdjTransport

set_option linter.style.header false

/-!
# `componentBlock (reassemble π F) v = π.part v`

Combines `reassemble_componentBlock_subset_part` (already proven) with the converse inclusion,
built from each block's own connectedness (`F B`'s `IsConnected`) transported into `reassemble`'s
`vertexGraph` via `reassemble_reachable_of_reachable_component`. The resulting
`componentPartition (reassemble π F) = π` equality, and the dependent per-block family equality,
remain future work.
-/

namespace SecondQuantization

variable {Mode : Type*} {N : ℕ}

/-- **`π.part v ⊆ componentBlock (reassemble π F) v`**: the converse of
`reassemble_componentBlock_subset_part`, using `F B`'s own connectedness. -/
theorem QuarticWickDiagram.part_subset_reassemble_componentBlock {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N))) (v : ↥S) :
    π.part (v : Fin N) ⊆ (QuarticWickDiagram.reassemble π F).componentBlock v := by
  intro x hx
  set B := (π.equivSigmaParts v).1 with hBdef
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

/-- **`componentBlock (reassemble π F) v = π.part v`**, in full. -/
theorem QuarticWickDiagram.reassemble_componentBlock_eq_part {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N))) (v : ↥S) :
    (QuarticWickDiagram.reassemble π F).componentBlock v = π.part (v : Fin N) :=
  Finset.Subset.antisymm (QuarticWickDiagram.reassemble_componentBlock_subset_part π F v)
    (QuarticWickDiagram.part_subset_reassemble_componentBlock π F v)

end SecondQuantization
