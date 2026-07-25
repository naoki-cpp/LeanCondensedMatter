import LeanCondensedMatter.SecondQuantization.Fermionic.WickDiagram.ReassembleComponentBlockEqPart

set_option linter.style.header false

/-!
# `componentPartition (reassemble π F) = π`

The `Finpartition` equality itself, from the pointwise `componentBlock (reassemble π F) v =
π.part v` agreement (`reassemble_componentBlock_eq_part`) already established. Two `Finpartition`s
of the same `s` agree iff their `parts` agree (`Finpartition.ext`), and both directions of that
`Finset` equality reduce to the pointwise agreement plus each `Finpartition`'s own basic API
(`part_mem`, `part_eq_of_mem`, `nonempty_of_mem_parts`).

The dependent per-block family equality (that `reassemble`'s own `restrictComponentConnected`
pieces, read back along this `componentPartition` equality, agree with `F` itself) remains future
work.
-/

namespace SecondQuantization

variable {Mode : Type*} {N : ℕ}

/-- **`componentPartition (reassemble π F) = π`.** -/
theorem QuarticWickDiagram.componentPartition_reassemble {S : Finset (Fin N)} (π : Finpartition S)
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
