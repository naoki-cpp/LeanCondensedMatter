import LeanCondensedMatter.Combinatorics.BinaryShuffleSlotEquiv
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ExternalVacuumReassembleLaws
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ExternalVacuumEquiv
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.OrderedConnectivity
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.InteractionVertexRelabelConnected
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.OrderedAmplitude

set_option linter.style.header false

/-!
# Reassembling external and vacuum diagrams along a binary slot shuffle

For fixed local external and vacuum interaction slots, a binary slot shuffle selects the ambient
interaction vertices occupied by the connected external core. The local diagrams are transported to
those two complementary subsets and reassembled by the existing Common external/vacuum constructor.
This is the structural presentation used by the one finite diagram-sum reindex in the external-leg
linked-cluster theorem.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Combinatorics.BinaryShuffle

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Arbitrary-set fixed-external diagrams whose complete graph is externally connected. -/
abbrev ExternallyConnectedFixedExternalTwoPointWickDiagramOn
    (Mode : Type*) (N : ℕ) (S : Finset (Fin N)) (i j : Mode) :=
  {d : FixedExternalTwoPointWickDiagramOn Mode N S i j // d.1.IsExternallyConnected}

noncomputable instance externallyConnectedFixedExternalTwoPointWickDiagramOnFintype
    (Mode : Type*) [Fintype Mode] (N : ℕ) (S : Finset (Fin N)) (i j : Mode) :
    Fintype (ExternallyConnectedFixedExternalTwoPointWickDiagramOn Mode N S i j) :=
  Fintype.ofFinite _

omit [LinearOrder Mode] [Fintype Mode] in
/-- The explicit diagram produced by the fixed-order equivalence is exactly the Common ordered
reindexing of the underlying arbitrary-set diagram. -/
theorem fixedExternalTwoPointWickDiagramOrderEquiv_val_eq_inInteractionOrder
    {N : ℕ} {S : Finset (Fin N)} (i j : Mode) (order : Common.QuarticVertexOrder S)
    (d : FixedExternalTwoPointWickDiagramOn Mode N S i j) :
    (fixedExternalTwoPointWickDiagramOrderEquiv i j order d).1 =
      d.1.inInteractionOrder order := by
  apply Common.TwoPointDiagram.ext
  · exact d.2.symm
  · funext v
    rfl
  · apply Combinatorics.Pairing.ext
    apply Equiv.ext
    intro leg
    apply Fin.ext
    rfl

omit [LinearOrder Mode] [Fintype Mode] in
/-- External connectedness is preserved by the fixed-order diagram equivalence. -/
theorem fixedExternalTwoPointWickDiagramOrderEquiv_isExternallyConnected_iff
    {N : ℕ} {S : Finset (Fin N)} (i j : Mode) (order : Common.QuarticVertexOrder S)
    (d : FixedExternalTwoPointWickDiagramOn Mode N S i j) :
    (fixedExternalTwoPointWickDiagramOrderEquiv i j order d).1.IsExternallyConnected ↔
      d.1.IsExternallyConnected := by
  rw [fixedExternalTwoPointWickDiagramOrderEquiv_val_eq_inInteractionOrder]
  exact d.1.inInteractionOrder_isExternallyConnected_iff order

/-- Restrict the fixed-order diagram equivalence to externally connected diagrams. -/
noncomputable def externallyConnectedFixedExternalTwoPointWickDiagramOrderEquiv
    {N : ℕ} {S : Finset (Fin N)} (i j : Mode) (order : Common.QuarticVertexOrder S) :
    ExternallyConnectedFixedExternalTwoPointWickDiagramOn Mode N S i j ≃
      ExternallyConnectedFixedExternalTwoPointWickDiagram Mode S.card i j :=
  (fixedExternalTwoPointWickDiagramOrderEquiv i j order).subtypeEquiv fun d =>
    (fixedExternalTwoPointWickDiagramOrderEquiv_isExternallyConnected_iff i j order d).symm

/-- Increasing order on the ambient slots occupied by the left side of a binary shuffle. -/
noncomputable def slotShuffleLeftVertexOrder {k m : ℕ} (shuffle : SlotShuffle k m) :
    Common.QuarticVertexOrder shuffle.leftSlots :=
  (finCongr shuffle.card_leftSlots).trans shuffle.leftSlotEquiv

/-- The right complement of a `k`-by-`m` slot shuffle has exactly `m` vertices. -/
theorem slotShuffleRightComplement_card {k m : ℕ} (shuffle : SlotShuffle k m) :
    ((Finset.univ : Finset (Fin (k + m))) \ shuffle.leftSlots).card = m := by
  have h := Fintype.card_congr shuffle.rightComplementEquiv
  simpa only [Fintype.card_coe, Fintype.card_fin] using h.symm

/-- Increasing order on the ambient complement occupied by the right side of a binary shuffle. -/
noncomputable def slotShuffleRightComplementVertexOrder {k m : ℕ}
    (shuffle : SlotShuffle k m) :
    Common.QuarticVertexOrder
      ((Finset.univ : Finset (Fin (k + m))) \ shuffle.leftSlots) :=
  (finCongr (slotShuffleRightComplement_card shuffle)).trans shuffle.rightComplementEquiv

/-- Reindex a quartic Wick diagram on an arbitrary finite vertex set to explicit `Fin |S|` slots. -/
noncomputable def quarticWickDiagramOrderEquiv {N : ℕ} {S : Finset (Fin N)}
    (order : Common.QuarticVertexOrder S) :
    QuarticWickDiagram Mode N S ≃
      QuarticWickDiagram Mode S.card (Finset.univ : Finset (Fin S.card)) := by
  let U : Finset (Fin S.card) := Finset.univ
  let hcard : U.card = S.card := by simp [U]
  let explicitOrder : Common.QuarticVertexOrder U :=
    (finCongr hcard).trans (Common.finEquivUnivSubtype S.card)
  exact (Common.quarticDiagramEquivOrderedData order).trans
    ((Equiv.cast
      (congrArg (Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode)) hcard).symm).trans
      (Common.quarticDiagramEquivOrderedData explicitOrder).symm)

/-- Transport explicit connected external diagrams to the left-slot subset of a shuffle. -/
noncomputable def connectedExternalOnSlotShuffleEquiv {k m : ℕ} (i j : Mode)
    (shuffle : SlotShuffle k m) :
    ExternallyConnectedFixedExternalTwoPointWickDiagram Mode k i j ≃
      ExternallyConnectedFixedExternalTwoPointWickDiagramOn
        Mode (k + m) shuffle.leftSlots i j :=
  (Equiv.cast
    (congrArg (fun n => ExternallyConnectedFixedExternalTwoPointWickDiagram Mode n i j)
      shuffle.card_leftSlots.symm)).trans
    (externallyConnectedFixedExternalTwoPointWickDiagramOrderEquiv
      i j (slotShuffleLeftVertexOrder shuffle)).symm

/-- Transport an explicit connected external diagram to the left-slot subset of a shuffle. -/
noncomputable def connectedExternalOnSlotShuffle {k m : ℕ} (i j : Mode)
    (external : ExternallyConnectedFixedExternalTwoPointWickDiagram Mode k i j)
    (shuffle : SlotShuffle k m) :
    ExternallyConnectedFixedExternalTwoPointWickDiagramOn
      Mode (k + m) shuffle.leftSlots i j :=
  connectedExternalOnSlotShuffleEquiv i j shuffle external

/-- Transport explicit vacuum Wick diagrams to the right-slot complement of a shuffle. -/
noncomputable def vacuumOnSlotShuffleEquiv {k m : ℕ} (shuffle : SlotShuffle k m) :
    QuarticWickDiagram Mode m (Finset.univ : Finset (Fin m)) ≃
      QuarticWickDiagram Mode (k + m)
        ((Finset.univ : Finset (Fin (k + m))) \ shuffle.leftSlots) :=
  (Equiv.cast
    (congrArg
      (fun n => QuarticWickDiagram Mode n (Finset.univ : Finset (Fin n)))
      (slotShuffleRightComplement_card shuffle).symm)).trans
    (quarticWickDiagramOrderEquiv
      (Mode := Mode) (slotShuffleRightComplementVertexOrder shuffle)).symm

/-- Transport an explicit vacuum Wick diagram to the right-slot complement of a shuffle. -/
noncomputable def vacuumOnSlotShuffle {k m : ℕ}
    (vacuum : QuarticWickDiagram Mode m (Finset.univ : Finset (Fin m)))
    (shuffle : SlotShuffle k m) :
    QuarticWickDiagram Mode (k + m)
      ((Finset.univ : Finset (Fin (k + m))) \ shuffle.leftSlots) :=
  vacuumOnSlotShuffleEquiv shuffle vacuum

/-- Reassemble one connected external diagram and one vacuum diagram according to a binary slot
shuffle. -/
noncomputable def reassembleExternalVacuumSlotShuffle {k m : ℕ} (i j : Mode)
    (external : ExternallyConnectedFixedExternalTwoPointWickDiagram Mode k i j)
    (vacuum : QuarticWickDiagram Mode m (Finset.univ : Finset (Fin m)))
    (shuffle : SlotShuffle k m) :
    FixedExternalTwoPointWickDiagram Mode (k + m) i j := by
  let externalOn := connectedExternalOnSlotShuffle i j external shuffle
  let vacuumOn := vacuumOnSlotShuffle vacuum shuffle
  refine ⟨Common.TwoPointDiagram.reassembleExternalVacuum
      (Finset.subset_univ shuffle.leftSlots) ⟨externalOn.1.1, externalOn.2⟩ vacuumOn, ?_⟩
  simpa [Common.TwoPointDiagram.reassembleExternalVacuum] using externalOn.1.2

omit [LinearOrder Mode] [Fintype Mode] in
/-- The reassembled diagram has exactly the shuffle's left slots in its external component. -/
theorem reassembleExternalVacuumSlotShuffle_externalInteractionPart {k m : ℕ} (i j : Mode)
    (external : ExternallyConnectedFixedExternalTwoPointWickDiagram Mode k i j)
    (vacuum : QuarticWickDiagram Mode m (Finset.univ : Finset (Fin m)))
    (shuffle : SlotShuffle k m) :
    Common.TwoPointDiagram.interactionPart
      ((reassembleExternalVacuumSlotShuffle i j external vacuum shuffle).1.externalComponent 0) =
      shuffle.leftSlots := by
  let externalOn := connectedExternalOnSlotShuffle i j external shuffle
  let vacuumOn := vacuumOnSlotShuffle vacuum shuffle
  change Common.TwoPointDiagram.interactionPart
      ((Common.TwoPointDiagram.reassembleExternalVacuum
        (Finset.subset_univ shuffle.leftSlots) ⟨externalOn.1.1, externalOn.2⟩ vacuumOn).externalComponent 0) =
    shuffle.leftSlots
  exact Common.TwoPointDiagram.interactionPart_externalComponent_reassembleExternalVacuum
    (Finset.subset_univ shuffle.leftSlots) ⟨externalOn.1.1, externalOn.2⟩ vacuumOn

/-- Explicit external core, explicit vacuum remainder, and the binary shuffle placing them into the
ambient interaction slots. -/
abbrev ExternalVacuumSlotData (Mode : Type*) (k m : ℕ) (i j : Mode) :=
  ExternallyConnectedFixedExternalTwoPointWickDiagram Mode k i j ×
    QuarticWickDiagram Mode m (Finset.univ : Finset (Fin m)) × SlotShuffle k m

/-- Reassemble binary slot data into one fixed-external diagram. -/
noncomputable def reassembleExternalVacuumSlotData {k m : ℕ} (i j : Mode)
    (x : ExternalVacuumSlotData Mode k m i j) :
    FixedExternalTwoPointWickDiagram Mode (k + m) i j :=
  reassembleExternalVacuumSlotShuffle i j x.1 x.2.1 x.2.2

/-- Binary slot reassembly is injective: the full diagram recovers its external slot set, hence the
shuffle, and fixed-subset reassembly then recovers both local diagrams. -/
theorem reassembleExternalVacuumSlotData_injective {k m : ℕ} (i j : Mode) :
    Function.Injective (reassembleExternalVacuumSlotData (Mode := Mode) (k := k) (m := m) i j) := by
  rintro ⟨external₁, vacuum₁, shuffle₁⟩ ⟨external₂, vacuum₂, shuffle₂⟩ hfull
  have hslots : shuffle₁.leftSlots = shuffle₂.leftSlots := by
    rw [← reassembleExternalVacuumSlotShuffle_externalInteractionPart
      i j external₁ vacuum₁ shuffle₁,
      ← reassembleExternalVacuumSlotShuffle_externalInteractionPart
        i j external₂ vacuum₂ shuffle₂]
    exact congrArg (fun d : FixedExternalTwoPointWickDiagram Mode (k + m) i j =>
      d.1.externalInteractionPart) hfull
  have hshuffle : shuffle₁ = shuffle₂ := SlotShuffle.eq_of_leftSlots_eq hslots
  subst shuffle₂
  let externalOn₁ := connectedExternalOnSlotShuffle i j external₁ shuffle₁
  let externalOn₂ := connectedExternalOnSlotShuffle i j external₂ shuffle₁
  let vacuumOn₁ := vacuumOnSlotShuffle vacuum₁ shuffle₁
  let vacuumOn₂ := vacuumOnSlotShuffle vacuum₂ shuffle₁
  have hpairs :
      (⟨externalOn₁.1.1, externalOn₁.2⟩, vacuumOn₁) =
        (⟨externalOn₂.1.1, externalOn₂.2⟩, vacuumOn₂) := by
    apply Common.TwoPointDiagram.reassembleExternalVacuum_injective_fixed
      (Finset.subset_univ shuffle₁.leftSlots)
    exact congrArg Subtype.val hfull
  have hextOn : externalOn₁ = externalOn₂ := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun p => p.1.1) hpairs
  have hvacOn : vacuumOn₁ = vacuumOn₂ := congrArg Prod.snd hpairs
  have hext : external₁ = external₂ :=
    (connectedExternalOnSlotShuffleEquiv i j shuffle₁).injective hextOn
  have hvac : vacuum₁ = vacuum₂ :=
    (vacuumOnSlotShuffleEquiv shuffle₁).injective hvacOn
  subst external₂
  subst vacuum₂
  rfl

/-- Fixed-external diagrams of total order `k+m` whose external component contains exactly `k`
interaction vertices. -/
abbrev FixedExternalTwoPointWickDiagramOfExternalOrder
    (Mode : Type*) (k m : ℕ) (i j : Mode) :=
  {d : FixedExternalTwoPointWickDiagram Mode (k + m) i j //
    d.1.externalInteractionPart.card = k}

/-- Reassemble slot data and remember the external-component order. -/
noncomputable def reassembleExternalVacuumSlotDataOfExternalOrder {k m : ℕ} (i j : Mode)
    (x : ExternalVacuumSlotData Mode k m i j) :
    FixedExternalTwoPointWickDiagramOfExternalOrder Mode k m i j :=
  ⟨reassembleExternalVacuumSlotData i j x, by
    rw [reassembleExternalVacuumSlotData,
      reassembleExternalVacuumSlotShuffle_externalInteractionPart]
    exact x.2.2.card_leftSlots⟩

/-- Every fixed-external diagram of external order `k` is obtained from a unique connected explicit
external core, explicit vacuum remainder, and binary slot shuffle. -/
theorem reassembleExternalVacuumSlotDataOfExternalOrder_surjective {k m : ℕ} (i j : Mode) :
    Function.Surjective
      (reassembleExternalVacuumSlotDataOfExternalOrder
        (Mode := Mode) (k := k) (m := m) i j) := by
  intro d
  let E : Finset (Fin (k + m)) := d.1.1.externalInteractionPart
  let shuffle : SlotShuffle k m :=
    (SlotShuffle.leftSlotSetEquiv k m).symm ⟨E, d.2⟩
  have hslots : shuffle.leftSlots = E := by
    have h := (SlotShuffle.leftSlotSetEquiv k m).apply_symm_apply ⟨E, d.2⟩
    exact congrArg Subtype.val h
  let externalOnE :
      ExternallyConnectedFixedExternalTwoPointWickDiagramOn Mode (k + m) E i j :=
    ⟨⟨d.1.1.restrictExternalComponent, d.1.2⟩,
      d.1.1.restrictExternalComponent_isExternallyConnected⟩
  let externalOn :
      ExternallyConnectedFixedExternalTwoPointWickDiagramOn
        Mode (k + m) shuffle.leftSlots i j := by
    rw [hslots]
    exact externalOnE
  let vacuumOnE : QuarticWickDiagram Mode (k + m)
      ((Finset.univ : Finset (Fin (k + m))) \ E) :=
    d.1.1.restrictVacuumRemainder
  let vacuumOn : QuarticWickDiagram Mode (k + m)
      ((Finset.univ : Finset (Fin (k + m))) \ shuffle.leftSlots) := by
    rw [hslots]
    exact vacuumOnE
  let external := (connectedExternalOnSlotShuffleEquiv i j shuffle).symm externalOn
  let vacuum := (vacuumOnSlotShuffleEquiv shuffle).symm vacuumOn
  refine ⟨(external, vacuum, shuffle), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have hext : connectedExternalOnSlotShuffle i j external shuffle = externalOn :=
    (connectedExternalOnSlotShuffleEquiv i j shuffle).apply_symm_apply externalOn
  have hvac : vacuumOnSlotShuffle vacuum shuffle = vacuumOn :=
    (vacuumOnSlotShuffleEquiv shuffle).apply_symm_apply vacuumOn
  change Common.TwoPointDiagram.reassembleExternalVacuum
      (Finset.subset_univ shuffle.leftSlots)
      ⟨(connectedExternalOnSlotShuffle i j external shuffle).1.1,
        (connectedExternalOnSlotShuffle i j external shuffle).2⟩
      (vacuumOnSlotShuffle vacuum shuffle) = d.1.1
  rw [hext, hvac]
  rw [hslots]
  exact d.1.1.reassemble_restrictExternal_restrictVacuumRemainder

/-- Binary slot data are equivalent to full fixed-external diagrams with a prescribed external
component order. -/
noncomputable def externalVacuumSlotDataEquivOfExternalOrder {k m : ℕ} (i j : Mode) :
    ExternalVacuumSlotData Mode k m i j ≃
      FixedExternalTwoPointWickDiagramOfExternalOrder Mode k m i j :=
  Equiv.ofBijective
    (reassembleExternalVacuumSlotDataOfExternalOrder
      (Mode := Mode) (k := k) (m := m) i j)
    ⟨fun x y h => reassembleExternalVacuumSlotData_injective i j
        (congrArg Subtype.val h),
      reassembleExternalVacuumSlotDataOfExternalOrder_surjective i j⟩

end Fermionic
end SecondQuantization
