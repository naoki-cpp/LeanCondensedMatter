import LeanCondensedMatter.SecondQuantization.Fermionic.WickDiagram.ReassembleDecompose

set_option linter.style.header false

/-!
# `reassemble`'s edges never cross a block: the first step of the "hard direction"

Towards `componentPartition (reassemble π F) = π` (the converse of `reassemble_componentPartition`,
still future work beyond this file): the first fact needed is that `reassemble π F`'s `vertexGraph`
never puts an edge between two different blocks of `π`, since `reassemblePairing` only ever pairs
legs within the same `Finpartition.equivSigmaParts` block (`bigLegEquiv`'s `Sigma` first component
is exactly that block, and `reassemblePairing` acts only on the second component via
`Equiv.sigmaCongrRight`).

`QuarticWickDiagram.reassemble_vertexGraph_adj_same_part` is that fact. Combined with each block's
own connectedness (from `F`) in a later PR, it will give `componentPartition (reassemble π F) = π`.
-/

namespace SecondQuantization

variable {Mode : Type*} {N : ℕ}

/-- **`bigLegEquiv`'s block (first component) at a leg is the leg's own vertex's `Finpartition`
part.** -/
theorem QuarticWickDiagram.bigLegEquiv_fst_eq_part {S : Finset (Fin N)} (π : Finpartition S)
    (leg : Fin (2 * (2 * S.card))) :
    ((QuarticWickDiagram.bigLegEquiv π leg).1 : Finset (Fin N)) =
      π.part (vertexOfLeg leg : Fin N) := by
  conv_lhs => rw [← QuarticWickDiagram.legOfVertexLocal_vertexOfLeg_localLegOfLeg leg]
  rw [QuarticWickDiagram.bigLegEquiv_legOfVertexLocal]
  rfl

/-- **`reassemble`'s pairing partner never changes `bigLegEquiv`'s block.** `reassemblePairing`
only permutes each `Sigma`-block's own legs among themselves (`Equiv.sigmaCongrRight`), so the
block (first component) is preserved by construction. -/
theorem QuarticWickDiagram.reassemble_partner_bigLegEquiv_fst {S : Finset (Fin N)}
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

/-- **`reassemble π F`'s `vertexGraph` never puts an edge between two different blocks of `π`.**
-/
theorem QuarticWickDiagram.reassemble_vertexGraph_adj_same_part {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N)))
    {u w : ↥S} (h : (QuarticWickDiagram.reassemble π F).vertexGraph.Adj u w) :
    π.part (u : Fin N) = π.part (w : Fin N) := by
  obtain ⟨-, leg, hu, hw⟩ := h
  rw [← hu, ← hw, ← QuarticWickDiagram.bigLegEquiv_fst_eq_part,
    ← QuarticWickDiagram.bigLegEquiv_fst_eq_part,
    QuarticWickDiagram.reassemble_partner_bigLegEquiv_fst]

end SecondQuantization
