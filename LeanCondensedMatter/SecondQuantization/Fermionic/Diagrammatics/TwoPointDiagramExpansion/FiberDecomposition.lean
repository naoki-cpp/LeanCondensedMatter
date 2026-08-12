import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.ConnectedSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram

set_option linter.style.header false

/-!
# The fiber decomposition for fixed external labels

`Common.TwoPointDiagram.externalFiberEquiv` decomposes the diagrams whose external component owns
exactly the slots `T` into an externally connected piece on `T` and an arbitrary quartic diagram on
the complement. Both halves of the splitting keep the external label — the piece carries the ambient
one, and reassembling carries the piece's — so the decomposition restricts to diagrams with the
external labels fixed to `Tτ cᵢ(τ) cⱼ†(τ')`.

That restricted form is what the linked-cluster convolution sums over.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {n : ℕ} {i j : Mode}

/-- Fixed-external two-point Wick diagrams on a chosen set of interaction slots. -/
abbrev FixedExternalTwoPointWickDiagramOn (Mode : Type*) (n : ℕ) (T : Finset (Fin n))
    (i j : Mode) : Type _ :=
  {d : TwoPointWickDiagram Mode n T // d.externalLabel = twoPointExternalLabels i j}

omit [LinearOrder Mode] [Fintype Mode] in
/-- The slot set owned by the external component, in the form the splitting lemmas expect. -/
theorem FixedExternalTwoPointWickDiagram.interactionPart_eq_of_externalSlots_eq
    {d : FixedExternalTwoPointWickDiagram Mode n i j} {T : Finset (Fin n)}
    (h : d.externalSlots = T) :
    Common.TwoPointDiagram.interactionPart (d.1.externalComponent 0) = T := h

/-- **The fiber decomposition with the external labels fixed.** The diagrams whose external
component owns exactly `T` are the pairs of an externally connected fixed-external diagram on `T`
and an arbitrary quartic diagram on the complementary slots. -/
noncomputable def fixedExternalFiberEquiv (T : Finset (Fin n)) :
    {d : FixedExternalTwoPointWickDiagram Mode n i j // d.externalSlots = T} ≃
      {ext : FixedExternalTwoPointWickDiagramOn Mode n T i j //
          ext.1.IsExternallyConnected} ×
        QuarticWickDiagram Mode n ((Finset.univ : Finset (Fin n)) \ T) where
  toFun d :=
    (⟨⟨d.1.1.slotSplitExternal (Finset.subset_univ T)
          (Common.isSplit_slotLegSplitting_of_interactionPart_eq (Finset.subset_univ T)
            (FixedExternalTwoPointWickDiagram.interactionPart_eq_of_externalSlots_eq d.2)),
        d.1.2⟩,
      Common.isExternallyConnected_slotSplitExternal (Finset.subset_univ T)
        (FixedExternalTwoPointWickDiagram.interactionPart_eq_of_externalSlots_eq d.2) _⟩,
     d.1.1.slotSplitVacuum (Finset.subset_univ T)
       (Common.isSplit_slotLegSplitting_of_interactionPart_eq (Finset.subset_univ T)
         (FixedExternalTwoPointWickDiagram.interactionPart_eq_of_externalSlots_eq d.2)))
  invFun p :=
    ⟨⟨Common.TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) p.1.1.1 p.2, p.1.1.2⟩,
      Common.interactionPart_externalComponent_ofSlotSplit (Finset.subset_univ T)
        p.1.1.1 p.2 p.1.2⟩
  left_inv d :=
    Subtype.ext (Subtype.ext
      (Common.TwoPointDiagram.ofSlotSplit_slotSplit (Finset.subset_univ T) d.1.1
        (Common.isSplit_slotLegSplitting_of_interactionPart_eq (Finset.subset_univ T)
          (FixedExternalTwoPointWickDiagram.interactionPart_eq_of_externalSlots_eq d.2))))
  right_inv p := by
    obtain ⟨⟨⟨ext, hlabel⟩, hconn⟩, vac⟩ := p
    simp only [Prod.mk.injEq]
    refine ⟨Subtype.ext (Subtype.ext ?_), ?_⟩
    · exact Common.TwoPointDiagram.slotSplitExternal_ofSlotSplit (Finset.subset_univ T)
        ext vac _
    · exact Common.TwoPointDiagram.slotSplitVacuum_ofSlotSplit (Finset.subset_univ T)
        ext vac _

end Fermionic
end SecondQuantization
