import LeanCondensedMatter.SecondQuantization.Fermionic.WickDiagram.ReassembleComponentPartitionEq

set_option linter.style.header false

/-!
# `(reassemble π F).restrictComponent hB' = (F B).1`

The last piece needed for the full mutual-inverse equivalence: for a block `B : π.parts`, the
restriction of `reassemble π F` back to `B` (using `componentPartition_reassemble` to identify `B`'s
membership in `(reassemble π F).componentPartition.parts` with its membership in `π.parts`)
reproduces `F B` exactly.

The key bridge is `reassembleVertex_eq_subtypeMemBlockEquiv_symm`: `reassembleVertex π B v` (used to
transport connectedness in `ReassembleBlockAdjTransport.lean`) and `restrictComponent`'s own
`subtypeMemBlockEquiv`-based embedding of `B`'s vertices into `↥S` are the *same* map. This lets
`π.equivSigmaParts` applied to a `restrictComponent`-embedded vertex be identified with a single
concrete `Sigma` value `⟨B, v⟩` in one atomic rewrite, avoiding the dependent-`Sigma` motive issues
that plague a naive component-by-component approach.
-/

namespace SecondQuantization

variable {Mode : Type*} {N : ℕ}

/-- **`reassembleVertex` agrees with `restrictComponent`'s own vertex embedding.** -/
theorem QuarticWickDiagram.reassembleVertex_eq_subtypeMemBlockEquiv_symm {S : Finset (Fin N)}
    (π : Finpartition S) (B : π.parts) (v : ↥(B : Finset (Fin N))) :
    QuarticWickDiagram.reassembleVertex π B v =
      ((QuarticWickDiagram.subtypeMemBlockEquiv (B : Finset (Fin N)) (π.le B.2)).symm v : ↥S) := by
  apply Subtype.ext
  change (π.equivSigmaParts.symm ⟨B, v⟩ : Fin N) = _
  rw [QuarticWickDiagram.subtypeMemBlockEquiv_symm_val]
  rfl

/-- **`π.equivSigmaParts` applied to a `restrictComponent`-embedded vertex is `⟨B, v⟩` itself.** -/
theorem QuarticWickDiagram.equivSigmaParts_subtypeMemBlockEquiv_symm {S : Finset (Fin N)}
    (π : Finpartition S) (B : π.parts) (v : ↥(B : Finset (Fin N))) :
    π.equivSigmaParts
        (((QuarticWickDiagram.subtypeMemBlockEquiv (B : Finset (Fin N)) (π.le B.2)).symm v : ↥S)) =
      ⟨B, v⟩ := by
  rw [← QuarticWickDiagram.reassembleVertex_eq_subtypeMemBlockEquiv_symm]
  exact π.equivSigmaParts.apply_symm_apply ⟨B, v⟩

/-- **`(reassemble π F).restrictComponent hB'`'s vertex labels agree with `F B`'s own.** The
vertex-label half of `(reassemble π F).restrictComponent hB' = (F B).1`. -/
theorem QuarticWickDiagram.restrictComponent_reassemble_vertexLabel {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N))) (B : π.parts)
    (hB' : (B : Finset (Fin N)) ∈ (QuarticWickDiagram.reassemble π F).componentPartition.parts)
    (v : ↥(B : Finset (Fin N))) :
    ((QuarticWickDiagram.reassemble π F).restrictComponent hB').vertexLabel v =
      (F B).1.vertexLabel v := by
  set u := (((QuarticWickDiagram.subtypeMemBlockEquiv (B : Finset (Fin N))
    ((QuarticWickDiagram.reassemble π F).componentPart_subset hB')).symm v : ↥S)) with hu
  change (F (π.equivSigmaParts u).1).1.vertexLabel (π.equivSigmaParts u).2 =
      (F B).1.vertexLabel v
  have hueq : u = ((QuarticWickDiagram.subtypeMemBlockEquiv (B : Finset (Fin N))
      (π.le B.2)).symm v : ↥S) := hu
  rw [hueq, QuarticWickDiagram.equivSigmaParts_subtypeMemBlockEquiv_symm]

end SecondQuantization
