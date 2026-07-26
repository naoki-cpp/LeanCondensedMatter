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

/-- **`blockLegEquiv`'s inverse for a reassembled block is `bigLegEquiv`'s inverse at that block.** -/
private theorem QuarticWickDiagram.blockLegEquiv_symm_reassemble_val {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N))) (B : π.parts)
    (hB' : (B : Finset (Fin N)) ∈ (QuarticWickDiagram.reassemble π F).componentPartition.parts)
    (leg : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    ((((QuarticWickDiagram.reassemble π F).blockLegEquiv hB').symm leg :
        {leg : Fin (2 * (2 * S.card)) //
          (QuarticWickDiagram.reassemble π F).legInBlock (B : Finset (Fin N)) leg}) :
        Fin (2 * (2 * S.card))) =
      (QuarticWickDiagram.bigLegEquiv π).symm ⟨B, leg⟩ := by
  rw [QuarticWickDiagram.bigLegEquiv_symm_sigma_mk]
  change legOfVertexLocal
      ((((QuarticWickDiagram.subtypeMemBlockEquiv (B : Finset (Fin N))
        ((QuarticWickDiagram.reassemble π F).componentPart_subset hB')).symm
          (vertexOfLeg leg) : {v : ↥S // (v : Fin N) ∈ (B : Finset (Fin N))}) : ↥S))
      (localLegOfLeg leg) =
    legOfVertexLocal (QuarticWickDiagram.reassembleVertex π B (vertexOfLeg leg))
      (localLegOfLeg leg)
  apply congrArg (fun v : ↥S => legOfVertexLocal v (localLegOfLeg leg))
  simpa using
    (QuarticWickDiagram.reassembleVertex_eq_subtypeMemBlockEquiv_symm π B
      (vertexOfLeg leg)).symm

/-- **`reassemble`'s partner acts by `F B`'s partner on a leg routed through block `B`.** -/
private theorem QuarticWickDiagram.reassemble_partner_bigLegEquiv_symm_sigma_mk
    {S : Finset (Fin N)} (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N))) (B : π.parts)
    (leg : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    (QuarticWickDiagram.reassemble π F).pairing.partner
        ((QuarticWickDiagram.bigLegEquiv π).symm ⟨B, leg⟩) =
      (QuarticWickDiagram.bigLegEquiv π).symm ⟨B, (F B).1.pairing.partner leg⟩ := by
  have hlhs : (QuarticWickDiagram.reassemble π F).pairing.partner =
      (QuarticWickDiagram.bigLegEquiv π).symm.permCongr
        (Equiv.sigmaCongrRight fun B => (F B).1.pairing.partner) := rfl
  rw [hlhs, Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  rfl

/-- **`(reassemble π F).restrictComponent hB'`'s pairing agrees with `F B`'s own.** -/
theorem QuarticWickDiagram.restrictComponent_reassemble_pairing {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N))) (B : π.parts)
    (hB' : (B : Finset (Fin N)) ∈ (QuarticWickDiagram.reassemble π F).componentPartition.parts) :
    ((QuarticWickDiagram.reassemble π F).restrictComponent hB').pairing = (F B).1.pairing := by
  change (QuarticWickDiagram.reassemble π F).restrictedPairing hB' = (F B).1.pairing
  apply Common.BlochDeDominicis.Pairing.ext
  apply Equiv.ext
  intro leg
  have hrestricted :=
    (QuarticWickDiagram.reassemble π F).restrictedPairing_partner_blockLegEquiv hB'
      (((QuarticWickDiagram.reassemble π F).blockLegEquiv hB').symm leg)
  rw [Equiv.apply_symm_apply] at hrestricted
  rw [hrestricted]
  apply ((QuarticWickDiagram.reassemble π F).blockLegEquiv hB').symm.injective
  rw [Equiv.symm_apply_apply]
  apply Subtype.ext
  rw [(QuarticWickDiagram.reassemble π F).restrictedPartner_val,
    QuarticWickDiagram.blockLegEquiv_symm_reassemble_val π F B hB' leg,
    QuarticWickDiagram.reassemble_partner_bigLegEquiv_symm_sigma_mk π F B leg,
    QuarticWickDiagram.blockLegEquiv_symm_reassemble_val π F B hB'
      ((F B).1.pairing.partner leg)]

/-- **Restricting `reassemble π F` back to block `B` reproduces `F B` exactly.** -/
theorem QuarticWickDiagram.restrictComponent_reassemble {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N))) (B : π.parts)
    (hB' : (B : Finset (Fin N)) ∈ (QuarticWickDiagram.reassemble π F).componentPartition.parts) :
    (QuarticWickDiagram.reassemble π F).restrictComponent hB' = (F B).1 := by
  refine QuarticWickDiagram.ext
    (funext fun v =>
      QuarticWickDiagram.restrictComponent_reassemble_vertexLabel π F B hB' v) ?_
  exact QuarticWickDiagram.restrictComponent_reassemble_pairing π F B hB'

end SecondQuantization
