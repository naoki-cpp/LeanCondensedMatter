import LeanCondensedMatter.Combinatorics.Shuffle.SlotShuffle
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Semantics.ExternalPiece
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.Wick.Diagram
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Components.ComponentDecomposition
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Core.SlotCongr
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplit.SlotSplitConnectivity

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

/-- A fixed-external two-point diagram on a chosen slot set, standardized by its increasing order
onto any `Fin m` whose size is identified by `h`. -/
noncomputable def fixedExternalTwoPointWickDiagramOnEquivOfCardEq
    (T : Finset (Fin n)) {m : ℕ} (h : T.card = m) :
    FixedExternalTwoPointWickDiagramOn Mode n T i j ≃
      FixedExternalTwoPointWickDiagram Mode m i j where
  toFun d :=
    ⟨d.1.slotCongr (Combinatorics.standardSlotEquivOfCardEq T h), by
      rw [Common.TwoPointDiagram.slotCongr_externalLabel]
      exact d.2⟩
  invFun d :=
    ⟨d.1.slotCongr (Combinatorics.standardSlotEquivOfCardEq T h).symm, by
      rw [Common.TwoPointDiagram.slotCongr_externalLabel]
      exact d.2⟩
  left_inv d :=
    Subtype.ext ((Common.TwoPointDiagram.slotCongrEquiv
      (Combinatorics.standardSlotEquivOfCardEq T h)).left_inv d.1)
  right_inv d :=
    Subtype.ext ((Common.TwoPointDiagram.slotCongrEquiv
      (Combinatorics.standardSlotEquivOfCardEq T h)).right_inv d.1)


/-- The increasing slot standardization with a chosen cardinality equality restricts to externally
connected fixed-external diagrams. -/
noncomputable def connectedFixedExternalTwoPointWickDiagramOnEquivOfCardEq
    (T : Finset (Fin n)) {m : ℕ} (h : T.card = m) :
    {ext : FixedExternalTwoPointWickDiagramOn Mode n T i j //
        ext.1.IsExternallyConnected} ≃
      {d : FixedExternalTwoPointWickDiagram Mode m i j //
        d.1.IsExternallyConnected} where
  toFun ext :=
    ⟨fixedExternalTwoPointWickDiagramOnEquivOfCardEq T h ext.1,
      (Common.TwoPointDiagram.slotCongr_isExternallyConnected_iff
        (Combinatorics.standardSlotEquivOfCardEq T h) ext.1.1).2 ext.2⟩
  invFun d :=
    ⟨(fixedExternalTwoPointWickDiagramOnEquivOfCardEq T h).symm d.1,
      (Common.TwoPointDiagram.slotCongr_isExternallyConnected_iff
        (Combinatorics.standardSlotEquivOfCardEq T h).symm d.1.1).2 d.2⟩
  left_inv ext :=
    Subtype.ext ((fixedExternalTwoPointWickDiagramOnEquivOfCardEq T h).left_inv ext.1)
  right_inv d :=
    Subtype.ext ((fixedExternalTwoPointWickDiagramOnEquivOfCardEq T h).right_inv d.1)


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
        QuarticWickDiagram Mode n ((Finset.univ : Finset (Fin n)) \ T) :=
  let e := Common.TwoPointDiagram.externalFiberEquiv (Finset.subset_univ T)
  { toFun d :=
      let p := e ⟨d.1.1, d.2⟩
      (⟨⟨p.1.1, d.1.2⟩, p.1.2⟩, p.2)
    invFun p :=
      let d := e.symm (⟨p.1.1.1, p.1.2⟩, p.2)
      ⟨⟨d.1, p.1.1.2⟩, d.2⟩
    left_inv d := by
      apply Subtype.ext
      apply Subtype.ext
      change (e.symm (e ⟨d.1.1, d.2⟩)).1 = d.1.1
      exact congrArg Subtype.val (e.left_inv ⟨d.1.1, d.2⟩)
    right_inv p := by
      have hr := e.right_inv (⟨p.1.1.1, p.1.2⟩, p.2)
      apply Prod.ext
      · apply Subtype.ext
        apply Subtype.ext
        change (e (e.symm (⟨p.1.1.1, p.1.2⟩, p.2))).1.1 = p.1.1.1
        exact congrArg (fun q => q.1.1) hr
      · change (e (e.symm (⟨p.1.1.1, p.1.2⟩, p.2))).2 = p.2
        exact congrArg Prod.snd hr
  }

omit [LinearOrder Mode] [Fintype Mode] in
/-- After reindexing a fiber, the standalone external piece at any identified slot count is exactly
the correspondingly standardized connected external diagram, independently of the vacuum piece. -/
theorem fixedExternalFiberEquiv_symm_externalPieceOfCardEq_eq
    (T : Finset (Fin n)) {m : ℕ} (h : T.card = m)
    (p : {ext : FixedExternalTwoPointWickDiagramOn Mode n T i j //
            ext.1.IsExternallyConnected} ×
          QuarticWickDiagram Mode n ((Finset.univ : Finset (Fin n)) \ T)) :
    let d := (fixedExternalFiberEquiv T).symm p
    let hsize : d.1.1.externalInteractionPart.card = m :=
      (congrArg Finset.card d.2).trans h
    d.1.externalPieceOfCardEq hsize =
      (connectedFixedExternalTwoPointWickDiagramOnEquivOfCardEq T h p.1).1 := by
  dsimp only
  let d := (fixedExternalFiberEquiv T).symm p
  let hsize : d.1.1.externalInteractionPart.card = m :=
    (congrArg Finset.card d.2).trans h
  change d.1.externalPieceOfCardEq hsize = _
  have hpiece :
      d.1.externalPieceOfCardEq hsize =
        fixedExternalTwoPointWickDiagramOnEquivOfCardEq T h
          ⟨d.1.1.slotSplitExternal (Finset.subset_univ T)
              (Common.isSplit_slotLegSplitting_of_interactionSector_eq
                (Finset.subset_univ T) d.2),
            d.1.2⟩ := by
    obtain ⟨d0, hd⟩ := d
    subst T
    have hh : hsize = h := Subsingleton.elim _ _
    rw [hh]
    apply Subtype.ext
    have hsplit :
        d0.1.externalVacuumSplit.1 =
          d0.1.slotSplitExternal (Finset.subset_univ d0.1.externalInteractionPart)
            (Common.isSplit_slotLegSplitting_of_interactionSector_eq
              (Finset.subset_univ d0.1.externalInteractionPart) rfl) := by
      rfl
    have hcongr := congrArg
      (fun x => Common.TwoPointDiagram.slotCongr
        (Combinatorics.standardSlotEquivOfCardEq d0.1.externalInteractionPart h) x) hsplit
    change
      Common.TwoPointDiagram.slotCongr
          (Combinatorics.standardSlotEquivOfCardEq d0.1.externalInteractionPart h)
          d0.1.externalVacuumSplit.1 =
        Common.TwoPointDiagram.slotCongr
          (Combinatorics.standardSlotEquivOfCardEq d0.1.externalInteractionPart h)
          (d0.1.slotSplitExternal
            (Finset.subset_univ d0.1.externalInteractionPart)
            (Common.isSplit_slotLegSplitting_of_interactionSector_eq
              (Finset.subset_univ d0.1.externalInteractionPart) rfl))
    exact hcongr
  have hright := (fixedExternalFiberEquiv T).apply_symm_apply p
  have hext :
      ⟨d.1.1.slotSplitExternal (Finset.subset_univ T)
          (Common.isSplit_slotLegSplitting_of_interactionSector_eq
            (Finset.subset_univ T) d.2), d.1.2⟩ = p.1.1 := by
    exact congrArg (fun q => q.1.1) hright
  rw [hext] at hpiece
  simpa [connectedFixedExternalTwoPointWickDiagramOnEquivOfCardEq] using hpiece

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
