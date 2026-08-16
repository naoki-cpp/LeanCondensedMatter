import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.DysonSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.ExternalPiece
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentDecomposition
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotCongr
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplitConnectivity

set_option linter.style.header false

/-!
# The fiber decomposition for fixed external labels

`Common.TwoPointDiagram.externalFiberEquiv` decomposes the diagrams whose external component owns
exactly the slots `T` into an externally connected piece on `T` and an arbitrary quartic diagram on
the complement. Both halves of the splitting keep the external label — the piece carries the ambient
one, and reassembling carries the piece's — so the decomposition restricts to diagrams with the
external labels fixed to `Tτ cᵢ(τ) cⱼ†(τ')`.

The same owner records how the standalone external piece behaves under this fiber equivalence. That
restricted form is what the linked-cluster convolution sums over.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {n : ℕ} {i j : Mode}

/-- Fixed-external two-point Wick diagrams on a chosen set of interaction slots. -/
abbrev FixedExternalTwoPointWickDiagramOn (Mode : Type*) (n : ℕ) (T : Finset (Fin n))
    (i j : Mode) : Type _ :=
  {d : TwoPointWickDiagram Mode n T // d.externalLabel = twoPointExternalLabels i j}

/-- A fixed-external two-point diagram on an arbitrary chosen slot set is canonically the same data
as an order-`|T|` fixed-external diagram, using the canonical increasing standardization of `T`. -/
noncomputable def fixedExternalTwoPointWickDiagramOnEquiv (T : Finset (Fin n)) :
    FixedExternalTwoPointWickDiagramOn Mode n T i j ≃
      FixedExternalTwoPointWickDiagram Mode T.card i j where
  toFun d :=
    ⟨d.1.slotCongr (Common.standardSlotEquiv T), by
      rw [Common.TwoPointDiagram.slotCongr_externalLabel]
      exact d.2⟩
  invFun d :=
    ⟨d.1.slotCongr (Common.standardSlotEquiv T).symm, by
      rw [Common.TwoPointDiagram.slotCongr_externalLabel]
      exact d.2⟩
  left_inv d :=
    Subtype.ext ((Common.TwoPointDiagram.slotCongrEquiv
      (Common.standardSlotEquiv T)).left_inv d.1)
  right_inv d :=
    Subtype.ext ((Common.TwoPointDiagram.slotCongrEquiv
      (Common.standardSlotEquiv T)).right_inv d.1)

/-- The canonical slot standardization restricts to externally connected fixed-external diagrams. -/
noncomputable def connectedFixedExternalTwoPointWickDiagramOnEquiv (T : Finset (Fin n)) :
    {ext : FixedExternalTwoPointWickDiagramOn Mode n T i j //
        ext.1.IsExternallyConnected} ≃
      {d : FixedExternalTwoPointWickDiagram Mode T.card i j //
        d.1.IsExternallyConnected} where
  toFun ext :=
    ⟨fixedExternalTwoPointWickDiagramOnEquiv T ext.1,
      (Common.TwoPointDiagram.slotCongr_isExternallyConnected_iff
        (Common.standardSlotEquiv T) ext.1.1).2 ext.2⟩
  invFun d :=
    ⟨(fixedExternalTwoPointWickDiagramOnEquiv T).symm d.1,
      (Common.TwoPointDiagram.slotCongr_isExternallyConnected_iff
        (Common.standardSlotEquiv T).symm d.1.1).2 d.2⟩
  left_inv ext := Subtype.ext ((fixedExternalTwoPointWickDiagramOnEquiv T).left_inv ext.1)
  right_inv d := Subtype.ext ((fixedExternalTwoPointWickDiagramOnEquiv T).right_inv d.1)

/-- Reassemble a fixed-external two-point diagram from a chosen external piece and quartic vacuum
piece. -/
noncomputable def fixedExternalOfSlotSplit (T : Finset (Fin n))
    (ext : FixedExternalTwoPointWickDiagramOn Mode n T i j)
    (vac : QuarticWickDiagram Mode n ((Finset.univ : Finset (Fin n)) \ T)) :
    FixedExternalTwoPointWickDiagram Mode n i j :=
  ⟨Common.TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext.1 vac, ext.2⟩

/-- **The fiber decomposition with the external labels fixed.** The diagrams whose external
component owns exactly `T` are the pairs of an externally connected fixed-external diagram on `T`
and an arbitrary quartic diagram on the complementary slots. -/
noncomputable def fixedExternalFiberEquiv (T : Finset (Fin n)) :
    {d : FixedExternalTwoPointWickDiagram Mode n i j // d.1.externalInteractionPart = T} ≃
      {ext : FixedExternalTwoPointWickDiagramOn Mode n T i j //
          ext.1.IsExternallyConnected} ×
        QuarticWickDiagram Mode n ((Finset.univ : Finset (Fin n)) \ T) where
  toFun d :=
    (⟨⟨d.1.1.slotSplitExternal (Finset.subset_univ T)
          (Common.isSplit_slotLegSplitting_of_interactionPart_eq (Finset.subset_univ T) d.2),
        d.1.2⟩,
      Common.isExternallyConnected_slotSplitExternal (Finset.subset_univ T) d.2 _⟩,
     d.1.1.slotSplitVacuum (Finset.subset_univ T)
       (Common.isSplit_slotLegSplitting_of_interactionPart_eq (Finset.subset_univ T) d.2))
  invFun p :=
    ⟨⟨Common.TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) p.1.1.1 p.2, p.1.1.2⟩,
      Common.interactionPart_externalComponent_ofSlotSplit (Finset.subset_univ T)
        p.1.1.1 p.2 p.1.2⟩
  left_inv d :=
    Subtype.ext (Subtype.ext
      (Common.TwoPointDiagram.ofSlotSplit_slotSplit (Finset.subset_univ T) d.1.1
        (Common.isSplit_slotLegSplitting_of_interactionPart_eq (Finset.subset_univ T) d.2)))
  right_inv p := by
    obtain ⟨⟨⟨ext, hlabel⟩, hconn⟩, vac⟩ := p
    simp only [Prod.mk.injEq]
    refine ⟨Subtype.ext (Subtype.ext ?_), ?_⟩
    · exact Common.TwoPointDiagram.slotSplitExternal_ofSlotSplit (Finset.subset_univ T)
        ext vac _
    · exact Common.TwoPointDiagram.slotSplitVacuum_ofSlotSplit (Finset.subset_univ T)
        ext vac _

omit [LinearOrder Mode] [Fintype Mode] in
/-- After reindexing a fiber by `fixedExternalFiberEquiv`, the ambient standalone external piece is
the standardized connected external diagram and therefore does not depend on the vacuum diagram. -/
theorem fixedExternalFiberEquiv_symm_externalPiece_heq
    (T : Finset (Fin n))
    (p : {ext : FixedExternalTwoPointWickDiagramOn Mode n T i j //
            ext.1.IsExternallyConnected} ×
          QuarticWickDiagram Mode n ((Finset.univ : Finset (Fin n)) \ T)) :
    HEq ((fixedExternalFiberEquiv T).symm p).1.externalPiece
      ((connectedFixedExternalTwoPointWickDiagramOnEquiv T p.1).1) := by
  let d := (fixedExternalFiberEquiv T).symm p
  have hpiece :
      HEq d.1.externalPiece
        (fixedExternalTwoPointWickDiagramOnEquiv T
          ⟨d.1.1.slotSplitExternal (Finset.subset_univ T)
              (Common.isSplit_slotLegSplitting_of_interactionPart_eq
                (Finset.subset_univ T) d.2),
            d.1.2⟩) := by
    obtain ⟨d, hd⟩ := d
    subst T
    apply heq_of_eq
    apply Subtype.ext
    have hsplit :
        d.1.externalVacuumSplit.1 =
          d.1.slotSplitExternal (Finset.subset_univ d.1.externalInteractionPart)
            (Common.isSplit_slotLegSplitting_of_interactionPart_eq
              (Finset.subset_univ d.1.externalInteractionPart) rfl) := by
      rfl
    have hcongr := congrArg
      (fun x => Common.TwoPointDiagram.slotCongr
        (Common.standardSlotEquiv d.1.externalInteractionPart) x) hsplit
    simpa [FixedExternalTwoPointWickDiagram.externalPiece,
      Common.TwoPointDiagram.externalPiece, fixedExternalTwoPointWickDiagramOnEquiv] using hcongr
  have hright := (fixedExternalFiberEquiv T).apply_symm_apply p
  have hext :
      ⟨d.1.1.slotSplitExternal (Finset.subset_univ T)
          (Common.isSplit_slotLegSplitting_of_interactionPart_eq
            (Finset.subset_univ T) d.2), d.1.2⟩ = p.1.1 := by
    exact congrArg (fun q => q.1.1) hright
  rw [hext] at hpiece
  exact hpiece

open Classical in
/-- **The diagram sum as a sum over the slot split.** Every fixed-external diagram is a connected
piece on the slots its external component owns and a vacuum diagram on the rest, so the sum over all
diagrams is the sum over that slot set of the sum over both pieces. -/
theorem sum_eq_sum_powerset_fixedExternalFiber {M : Type*} [AddCommMonoid M]
    (F : FixedExternalTwoPointWickDiagram Mode n i j → M) :
    (∑ d : FixedExternalTwoPointWickDiagram Mode n i j, F d) =
      ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
        ∑ p : {ext : FixedExternalTwoPointWickDiagramOn Mode n T i j //
              ext.1.IsExternallyConnected} ×
            QuarticWickDiagram Mode n ((Finset.univ : Finset (Fin n)) \ T),
          F ((fixedExternalFiberEquiv T).symm p).1 := by
  rw [(Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (FixedExternalTwoPointWickDiagram Mode n i j)))
    (t := (Finset.univ : Finset (Fin n)).powerset)
    (g := fun d : FixedExternalTwoPointWickDiagram Mode n i j => d.1.externalInteractionPart)
    (fun _ _ => Finset.mem_powerset.2 (Finset.subset_univ _)) F).symm]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.sum_subtype
    (p := fun d : FixedExternalTwoPointWickDiagram Mode n i j => d.1.externalInteractionPart = T)
    _ (fun x => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]) F]
  exact (Equiv.sum_comp (fixedExternalFiberEquiv T).symm (fun d => F d.1)).symm

end Fermionic
end SecondQuantization
