import LeanCondensedMatter.SecondQuantization.Fermionic.WickDiagram.ReassembleRestrictComponent

set_option linter.style.header false

/-!
# Quartic Wick diagram component-decomposition equivalence

Packages the component partition and connected component restrictions of a quartic Wick diagram as
an equivalence with a dependent family of connected diagrams, one on each partition block. The
inverse is `QuarticWickDiagram.reassemble`.

The two inverse laws are the previously proved `reassemble_componentPartition` and the converse
combination of `componentPartition_reassemble` with `restrictComponent_reassemble`.
-/

namespace SecondQuantization

variable {Mode : Type*} {N : ℕ}

/-- **A quartic Wick diagram decomposed into its component partition and connected pieces.** -/
noncomputable def QuarticWickDiagram.componentDecompose {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) :
    Σ π : Finpartition S,
      ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N)) :=
  ⟨d.componentPartition, fun B => d.restrictComponentConnected B.2⟩

/-- **Restricting a reassembled diagram as a connected diagram recovers the original block.** -/
theorem QuarticWickDiagram.restrictComponentConnected_reassemble {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N)))
    (B : π.parts)
    (hB' : (B : Finset (Fin N)) ∈ (QuarticWickDiagram.reassemble π F).componentPartition.parts) :
    (QuarticWickDiagram.reassemble π F).restrictComponentConnected hB' = F B := by
  apply Subtype.ext
  exact QuarticWickDiagram.restrictComponent_reassemble π F B hB'

private def QuarticWickDiagram.castBlock {S : Finset (Fin N)} {ρ π : Finpartition S}
    (h : ρ = π) (B : π.parts) : ρ.parts :=
  ⟨B.1, by rw [h]; exact B.2⟩

private theorem QuarticWickDiagram.componentFamily_transport_apply {S : Finset (Fin N)}
    {ρ π : Finpartition S} (h : ρ = π)
    (G : ∀ B : ρ.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N)))
    (B : π.parts) :
    (Eq.recOn (motive := fun σ _ =>
      ∀ C : σ.parts, ConnectedQuarticWickDiagram Mode N (C : Finset (Fin N))) h G) B =
      G (QuarticWickDiagram.castBlock h B) := by
  cases h
  rfl

private theorem QuarticWickDiagram.componentFamily_heq_of_eq {S : Finset (Fin N)}
    {ρ π : Finpartition S} (h : ρ = π)
    (G : ∀ B : ρ.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N)))
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N)))
    (hGF : ∀ B : π.parts, G (QuarticWickDiagram.castBlock h B) = F B) : HEq G F := by
  have hEq :
      Eq.recOn (motive := fun σ _ =>
        ∀ C : σ.parts, ConnectedQuarticWickDiagram Mode N (C : Finset (Fin N))) h G = F := by
    funext B
    rw [QuarticWickDiagram.componentFamily_transport_apply]
    exact hGF B
  exact (eqRec_heq h G).symm.trans (HEq.of_eq hEq)

/-- **The connected component family of a reassembled diagram is heterogeneously equal to `F`.** -/
private theorem QuarticWickDiagram.componentFamily_reassemble_heq {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N))) :
    HEq
      (fun B : (QuarticWickDiagram.reassemble π F).componentPartition.parts =>
        (QuarticWickDiagram.reassemble π F).restrictComponentConnected B.2)
      F := by
  let ρ := (QuarticWickDiagram.reassemble π F).componentPartition
  let G : ∀ B : ρ.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N)) :=
    fun B => (QuarticWickDiagram.reassemble π F).restrictComponentConnected B.2
  have hρ : ρ = π := by
    simpa [ρ] using QuarticWickDiagram.componentPartition_reassemble π F
  change HEq G F
  apply QuarticWickDiagram.componentFamily_heq_of_eq hρ G F
  intro B
  change (QuarticWickDiagram.reassemble π F).restrictComponentConnected
      (QuarticWickDiagram.castBlock hρ B).2 = F B
  exact QuarticWickDiagram.restrictComponentConnected_reassemble π F B
    (QuarticWickDiagram.castBlock hρ B).2

/-- **Decomposing a reassembled family recovers the original dependent family.** -/
theorem QuarticWickDiagram.componentDecompose_reassemble {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N))) :
    QuarticWickDiagram.componentDecompose (QuarticWickDiagram.reassemble π F) = ⟨π, F⟩ := by
  apply Sigma.ext
  · exact QuarticWickDiagram.componentPartition_reassemble π F
  · exact QuarticWickDiagram.componentFamily_reassemble_heq π F

end SecondQuantization
