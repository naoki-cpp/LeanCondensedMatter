import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ExternalSourceCumulant
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.InteractionPictureVertexDyson
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ExternalVacuumFiberCauchySum
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.MixedOrderData
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.ExternalPartition
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.BlockAssembly
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ComponentIntegral
import LeanCondensedMatter.Combinatorics.Cumulant.Moment
import Mathlib.Data.Fintype.EquivFin

set_option linter.style.header false

/-!
# Fermionic external-subset moments and connected-diagram contributions

Fix a finite, ordered family of external atomic fermion insertions.
Each even subset inherits the increasing order, field labels, and times.
Odd subsets have zero physical moments, as their pairing fibers are empty.
The empty source moment is defined to be one, independently of the interaction
order; the empty connected contribution is zero.

The weighted partition expression below is a precisely signed candidate for
the physical moment. Equality with the Dyson coefficients is a separate
combinatorial/analytic theorem: it requires the component restriction and
interaction-order shuffle to be summed over all diagram fibers. Defining a
partition sum is not a proof of that equality.
-/

namespace SecondQuantization
namespace Fermionic

open Common
open scoped BigOperators

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {E : ℕ}

/-- Canonical increasing reindexing of an even external subset, whose local
fermion field count is twice its pair count. -/
noncomputable def evenExternalSubsetOrderIso
    (S : Finset (Fin (2 * E))) (heven : Even S.card) :
    Fin (2 * (S.card / 2)) ≃o ↥S :=
  S.orderIsoOfFin (Nat.two_mul_div_two_of_even heven).symm

/-- Ordered external field labels restricted to an even subset. -/
noncomputable def evenExternalSubsetLabels
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (S : Finset (Fin (2 * E))) (heven : Even S.card) :
    Fin (2 * (S.card / 2)) → ExternalFieldLabel Mode :=
  fun i => labels (evenExternalSubsetOrderIso S heven i).1

/-- Ordered insertion times restricted to an even subset. -/
noncomputable def evenExternalSubsetTimes
    (times : Fin (2 * E) → ℝ)
    (S : Finset (Fin (2 * E))) (heven : Even S.card) :
    Fin (2 * (S.card / 2)) → ℝ :=
  fun i => times (evenExternalSubsetOrderIso S heven i).1

omit [LinearOrder Mode] [Fintype Mode] in
/-- Independently assembled Wick blocks have exactly the physically
restricted external-source labels in canonical increasing order. This
identifies the source-label part of the future actual-component/local-block
comparison without imposing or changing any source sign. -/
theorem ExternalInsertionBlockLayout.assembleDiagram_externalLabel_eq_evenExternalSubsetLabels
    {n : ℕ} (layout : ExternalInsertionBlockLayout E n)
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram (ExternalFieldLabel Mode) (QuarticVertexLabel Mode)
        ((B : Finset (Fin (2 * E))).card / 2) n
        (layout.interactionBlock (Finset.univ : Finset (Fin n)) B))
    (B : layout.partition.parts) :
    (F B).externalLabel =
      evenExternalSubsetLabels
        (layout.assembleDiagram (Finset.univ : Finset (Fin n)) F).externalLabel
        (B : Finset (Fin (2 * E))) (layout.evenBlocks B) := by
  classical
  funext i
  simpa only [evenExternalSubsetLabels, evenExternalSubsetOrderIso,
    layout.sourceEquiv_symm_apply] using
    (layout.assembleDiagram_externalLabel
      (Finset.univ : Finset (Fin n)) F B i).symm

omit [LinearOrder Mode] [Fintype Mode] in
/-- Restricting fixed external field labels by their canonical subset order
agrees definitionally with the labels on the standalone connected component. -/
theorem evenExternalSubsetLabels_componentOrderedDiagram
    {n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (B : d.vertexGraph.componentPartition.parts) :
    evenExternalSubsetLabels d.externalLabel
      ((B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n)))).toLeft)
      (d.externalSector_card_even B) =
        (d.componentOrderedDiagram B).externalLabel := by
  rfl

omit [LinearOrder Mode] [Fintype Mode] in
/-- The same increasing external-slot reindexing transports the actual
insertion times, without sorting by the imaginary-time value. -/
theorem evenExternalSubsetTimes_component
    {n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (times : Fin (2 * E) → ℝ)
    (B : d.vertexGraph.componentPartition.parts) :
    evenExternalSubsetTimes times
      ((B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n)))).toLeft)
      (d.externalSector_card_even B) =
        d.componentExternalTime times B := by
  rfl


/-- Restricting an external-field family to an even subset is invariant,
up to dependent equality, under equality of the actual source slot sets.
The two parity witnesses need not be definitionally the same. -/
private theorem evenExternalSubsetRestriction_heq_of_eq
    {Value : Type*} (F : Fin (2 * E) → Value)
    {S T : Finset (Fin (2 * E))}
    (hs : Even S.card) (ht : Even T.card) (hST : S = T) :
    HEq
      (fun i => F (evenExternalSubsetOrderIso S hs i).1)
      (fun i => F (evenExternalSubsetOrderIso T ht i).1) := by
  cases hST
  rfl

omit [LinearOrder Mode] [Fintype Mode] in
/-- In a physical assembly of independently connected Wick blocks, the
canonical standalone physical connected component has the same external
source labels as the originally supplied local diagram, up to the
dependent equality of its physically reconstructed external-pair count. -/
theorem ExternalInsertionBlockLayout.assembleDiagram_componentOrderedDiagram_externalLabel
    {n : ℕ} (layout : ExternalInsertionBlockLayout E n)
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram (ExternalFieldLabel Mode) (QuarticVertexLabel Mode)
        ((B : Finset (Fin (2 * E))).card / 2) n
        (layout.interactionBlock (Finset.univ : Finset (Fin n)) B))
    (hconnected : ∀ B, (F B).vertexGraph.Preconnected)
    (e : Fin (2 * E)) :
    HEq (F (layout.sourceEquiv e).1).externalLabel
      ((layout.assembleDiagram (Finset.univ : Finset (Fin n)) F).componentOrderedDiagram
        ⟨(layout.assembleDiagram (Finset.univ : Finset (Fin n)) F).vertexGraph.componentBlock
            (Sum.inl e),
          (layout.assembleDiagram (Finset.univ : Finset (Fin n)) F).vertexGraph.componentBlock_mem_componentPartition
            (Sum.inl e)⟩).externalLabel := by
  classical
  let d := layout.assembleDiagram (Finset.univ : Finset (Fin n)) F
  let B := (layout.sourceEquiv e).1
  let C : d.vertexGraph.componentPartition.parts :=
    ⟨d.vertexGraph.componentBlock (Sum.inl e),
      d.vertexGraph.componentBlock_mem_componentPartition (Sum.inl e)⟩
  have hsec : (B : Finset (Fin (2 * E))) =
      (C.1 : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n)))).toLeft :=
    (layout.assembleDiagram_componentExternalSector_external
      (Finset.univ : Finset (Fin n)) F hconnected e).symm
  have hlabels :
      (F B).externalLabel =
        evenExternalSubsetLabels d.externalLabel (B : Finset (Fin (2 * E)))
          (layout.evenBlocks B) :=
    ExternalInsertionBlockLayout.assembleDiagram_externalLabel_eq_evenExternalSubsetLabels layout F B
  have htransport :=
    evenExternalSubsetRestriction_heq_of_eq d.externalLabel
      (layout.evenBlocks B) (d.externalSector_card_even C) hsec
  have hcomponent := evenExternalSubsetLabels_componentOrderedDiagram (d := d) C
  exact (heq_of_eq hlabels).trans (htransport.trans (heq_of_eq hcomponent))

omit [LinearOrder Mode] [Fintype Mode] in
/-- An independently assembled connected block inherits exactly the
canonical source times from the physical assembled component. The local
source slots are increasing ambient slots, not reordered by their real
time values. This supplies the time-data transport for comparing genuine
local Dyson amplitudes with the extracted physical components. -/
theorem ExternalInsertionBlockLayout.assembleDiagram_componentExternalTime_eq_localTimes
    {n : ℕ} (layout : ExternalInsertionBlockLayout E n)
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram (ExternalFieldLabel Mode) (QuarticVertexLabel Mode)
        ((B : Finset (Fin (2 * E))).card / 2) n
        (layout.interactionBlock (Finset.univ : Finset (Fin n)) B))
    (hconnected : ∀ B, (F B).vertexGraph.Preconnected)
    (times : Fin (2 * E) → ℝ)
    (e : Fin (2 * E)) :
    HEq
      (fun i : Fin (2 * ((layout.sourceEquiv e).1.1.card / 2)) =>
        times (layout.sourceEquiv.symm ⟨(layout.sourceEquiv e).1, i⟩))
      ((layout.assembleDiagram (Finset.univ : Finset (Fin n)) F).componentExternalTime
        times
        ⟨(layout.assembleDiagram (Finset.univ : Finset (Fin n)) F).vertexGraph.componentBlock
            (Sum.inl e),
          (layout.assembleDiagram (Finset.univ : Finset (Fin n)) F).vertexGraph.componentBlock_mem_componentPartition
            (Sum.inl e)⟩) := by
  classical
  let d := layout.assembleDiagram (Finset.univ : Finset (Fin n)) F
  let B := (layout.sourceEquiv e).1
  let C : d.vertexGraph.componentPartition.parts :=
    ⟨d.vertexGraph.componentBlock (Sum.inl e),
      d.vertexGraph.componentBlock_mem_componentPartition (Sum.inl e)⟩
  have hsec : (B : Finset (Fin (2 * E))) =
      (C.1 : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n)))).toLeft :=
    (layout.assembleDiagram_componentExternalSector_external
      (Finset.univ : Finset (Fin n)) F hconnected e).symm
  have hlocal :
      (fun i : Fin (2 * (B.1.card / 2)) =>
        times (layout.sourceEquiv.symm ⟨B, i⟩)) =
        evenExternalSubsetTimes times (B : Finset (Fin (2 * E)))
          (layout.evenBlocks B) := by
    funext i
    simpa only [evenExternalSubsetTimes, evenExternalSubsetOrderIso] using
      congrArg times (layout.sourceEquiv_symm_apply B i)
  have htransport :=
    evenExternalSubsetRestriction_heq_of_eq times
      (layout.evenBlocks B) (d.externalSector_card_even C) hsec
  have hcomponent := evenExternalSubsetTimes_component (d := d) times C
  exact (heq_of_eq hlocal).trans (htransport.trans (heq_of_eq hcomponent))

omit [LinearOrder Mode] [Fintype Mode] in
/-- Pairing transport along an equality cast is only a change in the
dependent pair-count index; it does not change any Wick partners. -/
private theorem pairing_heq_of_finCongr_transport
    {a b : ℕ} (h : a = b) (P : Combinatorics.Pairing a)
    (Q : Combinatorics.Pairing b)
    (hpair : P.transport
      (finCongr (congrArg (fun k : ℕ => 2 * k) h)).symm = Q) :
    HEq P Q := by
  cases h
  have hc :
      (finCongr (congrArg (fun k : ℕ => 2 * k) (rfl : a = a))).symm =
        Equiv.refl (Fin (2 * a)) := by
    apply Equiv.ext
    intro i
    apply Fin.ext
    rfl
  rw [hc] at hpair
  have hself : P.transport (Equiv.refl _) = P := by
    apply Combinatorics.PairingOn.ext
    apply Equiv.ext
    intro i
    simp only [Combinatorics.PairingOn.transport_partner, Equiv.refl_apply,
      Equiv.refl_symm]
  rw [hself] at hpair
  exact heq_of_eq hpair

/-- Two dependent external-insertion diagrams are the same diagram
after equality of their external sizes and interaction supports, provided
their three original fields are equal in the heterogeneous sense. -/
private theorem externalInsertionDiagram_heq_of_fields
    {ExternalLabel InternalLabel : Type*} {E₁ E₂ n : ℕ}
    {S₁ S₂ : Finset (Fin n)}
    (hE : E₁ = E₂) (hS : S₁ = S₂)
    (p : ExternalInsertionDiagram ExternalLabel InternalLabel E₁ n S₁)
    (q : ExternalInsertionDiagram ExternalLabel InternalLabel E₂ n S₂)
    (he : HEq p.externalLabel q.externalLabel)
    (hv : HEq p.vertexLabel q.vertexLabel)
    (hp : HEq p.pairing q.pairing) :
    HEq p q := by
  cases hE
  cases hS
  exact heq_of_eq (ExternalInsertionDiagram.ext
    (eq_of_heq he) (eq_of_heq hv) (eq_of_heq hp))

omit [LinearOrder Mode] [Fintype Mode] in
/-- The *complete actual physically restricted graph component* is
the independently assembled connected Wick block, up to the dependent
equalities of its external-pair count and quartic-vertex subset.

Unlike separate label/vertex-weight/pair-sign comparisons, this identifies
the entire Wick diagram, including the actual oriented pairing.  It therefore
allows all concrete timed-field kernels to be transported by equality rather
than by an unjustified fermionic endpoint-symmetry assumption. -/
theorem ExternalInsertionBlockLayout.assembleDiagram_restrictComponent_heq_local
    {n : ℕ} (layout : ExternalInsertionBlockLayout E n)
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram (ExternalFieldLabel Mode) (QuarticVertexLabel Mode)
        ((B : Finset (Fin (2 * E))).card / 2) n
        (layout.interactionBlock (Finset.univ : Finset (Fin n)) B))
    (hconnected : ∀ B, (F B).vertexGraph.Preconnected)
    (e : Fin (2 * E)) :
    let d := layout.assembleDiagram (Finset.univ : Finset (Fin n)) F
    let C : d.vertexGraph.componentPartition.parts :=
      ⟨d.vertexGraph.componentBlock (Sum.inl e),
        d.vertexGraph.componentBlock_mem_componentPartition (Sum.inl e)⟩
    HEq (d.restrictComponent C) (F (layout.sourceEquiv e).1) := by
  classical
  let S : Finset (Fin n) := Finset.univ
  let B := (layout.sourceEquiv e).1
  let d := layout.assembleDiagram S F
  let C : d.vertexGraph.componentPartition.parts :=
    ⟨d.vertexGraph.componentBlock (Sum.inl e),
      d.vertexGraph.componentBlock_mem_componentPartition (Sum.inl e)⟩
  let T := interactionSector (C : Finset (ExternalInsertionVertex E S))
  let c := (d.componentBlockLegEquiv C).symm.trans
    (layout.physicalComponentLegEquiv S F hconnected e)
  have hsector : T = layout.interactionBlock S B :=
    layout.assembleDiagram_componentInteractionSector_external S F hconnected e
  have hcount : d.externalPairCount C = B.1.card / 2 :=
    layout.assembleDiagram_componentExternalPairCount_external S F hconnected e
  have hcards : 2 * T.card + d.externalPairCount C =
      2 * (layout.interactionBlock S B).card + B.1.card / 2 := by
    rw [hsector, hcount]
  have hcoord : c = finCongr (congrArg (fun k : ℕ => 2 * k) hcards) := by
    exact layout.physicalComponentCanonicalLegEquiv_eq_finCongr S F hconnected e
  have hpair :
      (d.restrictComponent C).pairing.transport
        (finCongr (congrArg (fun k : ℕ => 2 * k) hcards)).symm =
      (F B).pairing := by
    have hp := layout.physicalComponentCanonicalPairing_eq_local S F hconnected e
    change (d.restrictComponent C).pairing.transport c.symm = (F B).pairing at hp
    rwa [hcoord] at hp
  have hpairHeq : HEq (d.restrictComponent C).pairing (F B).pairing :=
    pairing_heq_of_finCongr_transport hcards _ _ hpair
  have hsrc : HEq (d.restrictComponent C).externalLabel (F B).externalLabel :=
    (ExternalInsertionBlockLayout.assembleDiagram_componentOrderedDiagram_externalLabel
      layout F hconnected e).symm
  have hvertex : HEq (d.restrictComponent C).vertexLabel (F B).vertexLabel :=
    (layout.assembleDiagram_restrictComponent_vertexLabel_heq S F hconnected e).symm
  exact externalInsertionDiagram_heq_of_fields hcount hsector
    (d.restrictComponent C) (F B) hsrc hvertex hpairHeq

/-- Canonical increasing interaction-slot standardization respects
heterogeneous equality of diagrams whose dependent source counts and
interaction supports have already been identified. -/
private theorem externalInsertionSlotCongr_heq_of_diagram_heq
    {ExternalLabel InternalLabel : Type*} {E₁ E₂ n : ℕ}
    {S₁ S₂ : Finset (Fin n)}
    (hE : E₁ = E₂) (hS : S₁ = S₂)
    (p : ExternalInsertionDiagram ExternalLabel InternalLabel E₁ n S₁)
    (q : ExternalInsertionDiagram ExternalLabel InternalLabel E₂ n S₂)
    (hp : HEq p q) :
    HEq (p.slotCongr (Combinatorics.standardSlotEquiv S₁))
      (q.slotCongr (Combinatorics.standardSlotEquiv S₂)) := by
  cases hE
  cases hS
  exact heq_of_eq (congrArg
    (fun d : ExternalInsertionDiagram ExternalLabel InternalLabel E₁ n S₁ =>
      d.slotCongr (Combinatorics.standardSlotEquiv S₁)) (eq_of_heq hp))

/-- Actual integrated Dyson amplitudes are invariant under simultaneous
dependent equality of their entire ordered Wick diagram and source-time
family. No sign or thermal-kernel symmetry is assumed. -/
private theorem dysonAmplitude_eq_of_diagram_time_heq
    {E₁ E₂ n₁ n₂ : ℕ} (hE : E₁ = E₂) (hn : n₁ = n₂)
    (p : ExternalInsertionWickDiagram Mode E₁ n₁)
    (q : ExternalInsertionWickDiagram Mode E₂ n₂)
    (hp : HEq p q)
    (t₁ : Fin (2 * E₁) → ℝ) (t₂ : Fin (2 * E₂) → ℝ)
    (ht : HEq t₁ t₂)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) :
    p.dysonAmplitude ε β g t₁ = q.dysonAmplitude ε β g t₂ := by
  cases hE
  cases hn
  have hd : p = q := eq_of_heq hp
  have ht' : t₁ = t₂ := eq_of_heq ht
  rw [hd, ht']

/-- The integrated Dyson amplitude of an *actual physical connected
component*, with its original source times, is exactly the integrated
Dyson amplitude of the independently supplied connected Wick block
after its canonical increasing interaction-slot standardization.

In particular this establishes the concrete free-Gibbs contraction-kernel
compatibility by equality of the complete timed Wick data. It neither
exchanges fermionic pair endpoints nor assumes that one ordered simplex
integral factors before summing over component shuffles. -/
theorem ExternalInsertionBlockLayout.assembleConnectedBlocks_componentDysonAmplitude_eq_local
    {n : ℕ} (layout : ExternalInsertionBlockLayout E n)
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram (ExternalFieldLabel Mode) (QuarticVertexLabel Mode)
        ((B : Finset (Fin (2 * E))).card / 2) n
        (layout.interactionBlock (Finset.univ : Finset (Fin n)) B))
    (hconnected : ∀ B, (F B).vertexGraph.Preconnected)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) (e : Fin (2 * E)) :
    let d : ExternalInsertionWickDiagram Mode E n :=
      layout.assembleDiagram (Finset.univ : Finset (Fin n)) F
    let C : d.vertexGraph.componentPartition.parts :=
      ⟨d.vertexGraph.componentBlock (Sum.inl e),
        d.vertexGraph.componentBlock_mem_componentPartition (Sum.inl e)⟩
    ExternalInsertionWickDiagram.dysonAmplitude (d.componentOrderedDiagram C) ε β g
        (d.componentExternalTime externalTime C) =
      ExternalInsertionWickDiagram.dysonAmplitude
        ((F (layout.sourceEquiv e).1).slotCongr
          (Combinatorics.standardSlotEquiv
            (layout.interactionBlock (Finset.univ : Finset (Fin n))
              (layout.sourceEquiv e).1))) ε β g
        (fun i => externalTime
          (layout.sourceEquiv.symm ⟨(layout.sourceEquiv e).1, i⟩)) := by
  classical
  let S : Finset (Fin n) := Finset.univ
  let B := (layout.sourceEquiv e).1
  let d : ExternalInsertionWickDiagram Mode E n := layout.assembleDiagram S F
  let C : d.vertexGraph.componentPartition.parts :=
    ⟨d.vertexGraph.componentBlock (Sum.inl e),
      d.vertexGraph.componentBlock_mem_componentPartition (Sum.inl e)⟩
  let T := interactionSector (C : Finset (ExternalInsertionVertex E S))
  have hsector : T = layout.interactionBlock S B :=
    layout.assembleDiagram_componentInteractionSector_external S F hconnected e
  have hcount : d.externalPairCount C = B.1.card / 2 :=
    layout.assembleDiagram_componentExternalPairCount_external S F hconnected e
  have hphysical : HEq (d.restrictComponent C) (F B) :=
    ExternalInsertionBlockLayout.assembleDiagram_restrictComponent_heq_local
      layout F hconnected e
  have hordered : HEq (d.componentOrderedDiagram C)
      ((F B).slotCongr (Combinatorics.standardSlotEquiv
        (layout.interactionBlock S B))) := by
    have hslot := externalInsertionSlotCongr_heq_of_diagram_heq
      hcount hsector (d.restrictComponent C) (F B) hphysical
    exact (heq_of_eq (d.componentOrderedDiagram_eq_slotCongr C)).trans hslot
  have htimes : HEq (d.componentExternalTime externalTime C)
      (fun i : Fin (2 * (B.1.card / 2)) =>
        externalTime (layout.sourceEquiv.symm ⟨B, i⟩)) :=
    (ExternalInsertionBlockLayout.assembleDiagram_componentExternalTime_eq_localTimes
      layout F hconnected externalTime e).symm
  exact dysonAmplitude_eq_of_diagram_time_heq
    hcount (congrArg Finset.card hsector)
    (d.componentOrderedDiagram C)
    ((F B).slotCongr (Combinatorics.standardSlotEquiv
      (layout.interactionBlock S B))) hordered
    (d.componentExternalTime externalTime C)
    (fun i => externalTime (layout.sourceEquiv.symm ⟨B, i⟩))
    htimes ε β g

/-- The genuine **integrated physical component-shuffle orbit**
of assembled connected Wick blocks equals the source-partition Koszul sign
times the product of the *original independent local Dyson amplitudes*.

Every local factor carries its actual labels, contracted Wick pairing,
original restricted source times, and canonical increasing interaction-slot
order. The product is indexed by the prescribed external partition rather
than an unverified choice of graph components. The equality is only after
the complete interaction-order shuffle sum; it does not factor an
individual ordered-simplex integral. -/
theorem ExternalInsertionBlockLayout.assembleConnectedBlocks_signedDysonShuffleOrbit_eq_independentLocals
    {n : ℕ} (layout : ExternalInsertionBlockLayout E n)
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram (ExternalFieldLabel Mode) (QuarticVertexLabel Mode)
        ((B : Finset (Fin (2 * E))).card / 2) n
        (layout.interactionBlock (Finset.univ : Finset (Fin n)) B))
    (hconnected : ∀ B, (F B).vertexGraph.Preconnected)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) :
    let d : ExternalInsertionWickDiagram Mode E n :=
      layout.assembleDiagram (Finset.univ : Finset (Fin n)) F
    (∑ shuffle : d.ComponentInteractionOrderShuffle,
      d.orderedDysonAmplitude ε β g externalTime
        (d.assembleInteractionOrder d.canonicalComponentInteractionOrders shuffle)) =
      externalPartitionSourceSign layout.partition *
        ∏ B : layout.partition.parts,
          ExternalInsertionWickDiagram.dysonAmplitude
            ((F B).slotCongr (Combinatorics.standardSlotEquiv
              (layout.interactionBlock (Finset.univ : Finset (Fin n)) B)))
            ε β g (fun i => externalTime (layout.sourceEquiv.symm ⟨B, i⟩)) := by
  classical
  let S : Finset (Fin n) := Finset.univ
  let d : ExternalInsertionWickDiagram Mode E n := layout.assembleDiagram S F
  have hVac : HasNoVacuumComponent d.vertexGraph :=
    layout.hasNoVacuumComponent_assembleDiagram S F hconnected
  have hpart : externalComponentPartition d.vertexGraph = layout.partition :=
    layout.externalComponentPartition_assembleDiagram S F hconnected
  let partsEquiv :
      (externalComponentPartition d.vertexGraph).parts ≃ layout.partition.parts :=
    { toFun := fun P => ⟨P.1, by rw [← hpart]; exact P.2⟩
      invFun := fun P => ⟨P.1, by rw [hpart]; exact P.2⟩
      left_inv := fun P => Subtype.ext rfl
      right_inv := fun P => Subtype.ext rfl }
  let reindex : d.vertexGraph.componentPartition.parts ≃ layout.partition.parts :=
    (d.vacuumFreeComponentsEquivExternalBlocks hVac).trans partsEquiv
  have hblock (C : d.vertexGraph.componentPartition.parts) :
      (reindex C : Finset (Fin (2 * E))) =
        (C.1 : Finset (ExternalInsertionVertex E S)).toLeft :=
    d.vacuumFreeComponentsEquivExternalBlocks_apply hVac C
  have hlocal (B : layout.partition.parts) :
      ExternalInsertionWickDiagram.dysonAmplitude
          (d.componentOrderedDiagram (reindex.symm B)) ε β g
          (d.componentExternalTime externalTime (reindex.symm B)) =
        ExternalInsertionWickDiagram.dysonAmplitude
          ((F B).slotCongr (Combinatorics.standardSlotEquiv
            (layout.interactionBlock S B)))
          ε β g (fun i => externalTime (layout.sourceEquiv.symm ⟨B, i⟩)) := by
    have hnonempty : (B : Finset (Fin (2 * E))).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr (layout.partition.ne_bot B.2)
    obtain ⟨e, he⟩ := hnonempty
    have hsource : (layout.sourceEquiv e).1 = B := by
      apply Subtype.ext
      simpa only [layout.sourceEquiv_fst] using
        (layout.partition.part_eq_of_mem B.2 he)
    have hmem : (Sum.inl e : ExternalInsertionVertex E S) ∈
        ((reindex.symm B).1 : Finset (ExternalInsertionVertex E S)) := by
      apply Finset.mem_toLeft.mp
      rw [← hblock (reindex.symm B), Equiv.apply_symm_apply]
      exact he
    have hC :
        reindex.symm B =
          ⟨d.vertexGraph.componentBlock (Sum.inl e),
            d.vertexGraph.componentBlock_mem_componentPartition (Sum.inl e)⟩ := by
      apply Subtype.ext
      exact ((d.vertexGraph.componentBlock_eq_iff_mem
        (reindex.symm B).2 (Sum.inl e)).2 hmem).symm
    rw [hC]
    have h := ExternalInsertionBlockLayout.assembleConnectedBlocks_componentDysonAmplitude_eq_local
      layout F hconnected ε β g externalTime e
    rw [hsource] at h
    simpa only [d, S] using h
  have horbit := ExternalInsertionBlockLayout.assembleConnectedBlocks_signedDysonShuffleOrbit
    layout F hconnected ε β g externalTime
  rw [horbit]
  apply congrArg (fun z : ℂ => externalPartitionSourceSign layout.partition * z)
  exact (Equiv.prod_comp reindex.symm
    (fun C : d.vertexGraph.componentPartition.parts =>
      ExternalInsertionWickDiagram.dysonAmplitude
        (d.componentOrderedDiagram C) ε β g
        (d.componentExternalTime externalTime C))).symm.trans
    (Finset.prod_congr rfl (fun B _ => hlocal B))

omit [LinearOrder Mode] [Fintype Mode] in
/-- The source labels of an assembled diagram agree with the canonical
increasing restriction on *each* external block.  This converts the
independent-block label predicate into the source-subset convention used
by the connected Dyson series, without changing any interaction owners. -/
theorem ExternalInsertionBlockLayout.assembleDiagram_externalLabel_eq_iff_evenSubsetLabels
    {n : ℕ} (layout : ExternalInsertionBlockLayout E n)
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram (ExternalFieldLabel Mode) (QuarticVertexLabel Mode)
        ((B : Finset (Fin (2 * E))).card / 2) n
        (layout.interactionBlock (Finset.univ : Finset (Fin n)) B))
    (labels : Fin (2 * E) → ExternalFieldLabel Mode) :
    (layout.assembleDiagram (Finset.univ : Finset (Fin n)) F).externalLabel = labels ↔
      ∀ B : layout.partition.parts,
        (F B).externalLabel =
          evenExternalSubsetLabels labels (B : Finset (Fin (2 * E)))
            (layout.evenBlocks B) := by
  rw [layout.assembleDiagram_externalLabel_eq_iff
    (Finset.univ : Finset (Fin n)) F labels]
  constructor
  · intro h B
    calc
      (F B).externalLabel =
          (fun i => labels (layout.sourceEquiv.symm ⟨B, i⟩)) := h B
      _ = evenExternalSubsetLabels labels (B : Finset (Fin (2 * E)))
            (layout.evenBlocks B) := by
        funext i
        rw [layout.sourceEquiv_symm_apply B i]
        rfl
  · intro h B
    calc
      (F B).externalLabel =
          evenExternalSubsetLabels labels (B : Finset (Fin (2 * E)))
            (layout.evenBlocks B) := h B
      _ = (fun i => labels (layout.sourceEquiv.symm ⟨B, i⟩)) := by
        funext i
        rw [layout.sourceEquiv_symm_apply B i]
        rfl

/-- The physical connected-block Dyson shuffle orbit, now expressed using
the canonical increasing *subset restriction* of external insertion times.
These are exactly the times appearing in each connected source-subset
coefficient.  Only the full shuffle sum, never a single simplex integral,
is replaced by the product of local integrated amplitudes. -/
theorem ExternalInsertionBlockLayout.assembleConnectedBlocks_signedDysonShuffleOrbit_eq_subsetTimes
    {n : ℕ} (layout : ExternalInsertionBlockLayout E n)
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram (ExternalFieldLabel Mode) (QuarticVertexLabel Mode)
        ((B : Finset (Fin (2 * E))).card / 2) n
        (layout.interactionBlock (Finset.univ : Finset (Fin n)) B))
    (hconnected : ∀ B, (F B).vertexGraph.Preconnected)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (times : Fin (2 * E) → ℝ) :
    let d : ExternalInsertionWickDiagram Mode E n :=
      layout.assembleDiagram (Finset.univ : Finset (Fin n)) F
    (∑ shuffle : d.ComponentInteractionOrderShuffle,
      d.orderedDysonAmplitude ε β g times
        (d.assembleInteractionOrder d.canonicalComponentInteractionOrders shuffle)) =
      externalPartitionSourceSign layout.partition *
        ∏ B : layout.partition.parts,
          ExternalInsertionWickDiagram.dysonAmplitude
            ((F B).slotCongr (Combinatorics.standardSlotEquiv
              (layout.interactionBlock (Finset.univ : Finset (Fin n)) B)))
            ε β g (evenExternalSubsetTimes times
              (B : Finset (Fin (2 * E))) (layout.evenBlocks B)) := by
  classical
  have htime (B : layout.partition.parts) :
      (fun i => times (layout.sourceEquiv.symm ⟨B, i⟩)) =
        evenExternalSubsetTimes times (B : Finset (Fin (2 * E)))
          (layout.evenBlocks B) := by
    funext i
    rw [layout.sourceEquiv_symm_apply B i]
    rfl
  simpa only [htime] using
    (ExternalInsertionBlockLayout.assembleConnectedBlocks_signedDysonShuffleOrbit_eq_independentLocals
      layout F hconnected ε β g times)

open Classical in
/-- At a fixed physical external-block layout, summing the **actual
integrated** component-shuffle orbit over every independent preconnected
Wick-block family with the prescribed source labels gives the source
Koszul sign times the product of the corresponding connected local
Dyson amplitude sums.

Unlike an unjustified factorization of one ordered-simplex integral, this
first sums the complete physical interaction-shuffle orbit, then invokes
the independent finite connected-block sum factorization. All block
interaction fibers, including zero-size fibers, are retained. -/
theorem ExternalInsertionBlockLayout.sum_signedDysonShuffleOrbits_eq_prod_connectedBlocks
    {n : ℕ} (layout : ExternalInsertionBlockLayout E n)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (times : Fin (2 * E) → ℝ) :
    (∑ F : layout.ConnectedBlockFamily
        (ExternalLabel := ExternalFieldLabel Mode)
        (InternalLabel := QuarticVertexLabel Mode),
      if ∀ B : layout.partition.parts,
          (F.1 B).externalLabel =
            evenExternalSubsetLabels labels (B : Finset (Fin (2 * E)))
              (layout.evenBlocks B) then
        let d : ExternalInsertionWickDiagram Mode E n :=
          layout.assembleDiagram (Finset.univ : Finset (Fin n)) F.1
        ∑ shuffle : d.ComponentInteractionOrderShuffle,
          d.orderedDysonAmplitude ε β g times
            (d.assembleInteractionOrder d.canonicalComponentInteractionOrders shuffle)
      else 0) =
      externalPartitionSourceSign layout.partition *
        ∏ B : layout.partition.parts,
          ∑ d : {d : ExternalInsertionDiagram
              (ExternalFieldLabel Mode) (QuarticVertexLabel Mode)
              ((B : Finset (Fin (2 * E))).card / 2) n
              (layout.interactionBlock (Finset.univ : Finset (Fin n)) B) //
                d.vertexGraph.Preconnected},
            if d.1.externalLabel =
                evenExternalSubsetLabels labels (B : Finset (Fin (2 * E)))
                  (layout.evenBlocks B) then
              ExternalInsertionWickDiagram.dysonAmplitude
                (d.1.slotCongr (Combinatorics.standardSlotEquiv
                  (layout.interactionBlock (Finset.univ : Finset (Fin n)) B)))
                ε β g (evenExternalSubsetTimes times
                  (B : Finset (Fin (2 * E))) (layout.evenBlocks B))
            else 0 := by
  classical
  let condition : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram (ExternalFieldLabel Mode) (QuarticVertexLabel Mode)
        ((B : Finset (Fin (2 * E))).card / 2) n
        (layout.interactionBlock (Finset.univ : Finset (Fin n)) B) → Prop :=
    fun B d => d.externalLabel =
      evenExternalSubsetLabels labels (B : Finset (Fin (2 * E)))
        (layout.evenBlocks B)
  let weight : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram (ExternalFieldLabel Mode) (QuarticVertexLabel Mode)
        ((B : Finset (Fin (2 * E))).card / 2) n
        (layout.interactionBlock (Finset.univ : Finset (Fin n)) B) → ℂ :=
    fun B d =>
      ExternalInsertionWickDiagram.dysonAmplitude
        (d.slotCongr (Combinatorics.standardSlotEquiv
          (layout.interactionBlock (Finset.univ : Finset (Fin n)) B)))
        ε β g (evenExternalSubsetTimes times
          (B : Finset (Fin (2 * E))) (layout.evenBlocks B))
  have horbit (F : layout.ConnectedBlockFamily
      (ExternalLabel := ExternalFieldLabel Mode)
      (InternalLabel := QuarticVertexLabel Mode)) :
      (let d : ExternalInsertionWickDiagram Mode E n :=
        layout.assembleDiagram (Finset.univ : Finset (Fin n)) F.1
      ∑ shuffle : d.ComponentInteractionOrderShuffle,
        d.orderedDysonAmplitude ε β g times
          (d.assembleInteractionOrder d.canonicalComponentInteractionOrders shuffle)) =
        externalPartitionSourceSign layout.partition *
          ∏ B, weight B (F.1 B) := by
    simpa only [weight] using
      (ExternalInsertionBlockLayout.assembleConnectedBlocks_signedDysonShuffleOrbit_eq_subsetTimes
        layout F.1 F.2 ε β g times)
  calc
    _ = ∑ F : layout.ConnectedBlockFamily
        (ExternalLabel := ExternalFieldLabel Mode)
        (InternalLabel := QuarticVertexLabel Mode),
        if ∀ B, condition B (F.1 B) then
          externalPartitionSourceSign layout.partition * ∏ B, weight B (F.1 B)
        else 0 := by
      apply Finset.sum_congr rfl
      intro F _
      exact if_congr Iff.rfl (horbit F) rfl
    _ = externalPartitionSourceSign layout.partition *
        ∑ F : layout.ConnectedBlockFamily
          (ExternalLabel := ExternalFieldLabel Mode)
          (InternalLabel := QuarticVertexLabel Mode),
          if ∀ B, condition B (F.1 B) then
            ∏ B, weight B (F.1 B)
          else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro F _
      split_ifs <;> simp
    _ = _ := by
      simpa only [condition, weight] using
        (congrArg (fun z : ℂ => externalPartitionSourceSign layout.partition * z)
          (layout.sum_connectedBlockFamilies_prod_if condition weight))

open Classical in
/-- Canonically standardizing the interaction vertices of one connected
external-source block reindexes the *entire finite local Wick diagram sum*,
including its prescribed external field labels and actual integrated
Dyson amplitudes. Consequently a local sum depends only on the block's
interaction-vertex cardinality, not its ambient owner subset. -/
theorem ExternalInsertionBlockLayout.sum_preconnectedDysonBlock_eq_standardized
    {n : ℕ} (layout : ExternalInsertionBlockLayout E n)
    (B : layout.partition.parts)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (times : Fin (2 * E) → ℝ) :
    (∑ d : {d : ExternalInsertionDiagram
        (ExternalFieldLabel Mode) (QuarticVertexLabel Mode)
        ((B : Finset (Fin (2 * E))).card / 2) n
        (layout.interactionBlock (Finset.univ : Finset (Fin n)) B) //
        d.vertexGraph.Preconnected},
      if d.1.externalLabel =
          evenExternalSubsetLabels labels (B : Finset (Fin (2 * E)))
            (layout.evenBlocks B) then
        ExternalInsertionWickDiagram.dysonAmplitude
          (d.1.slotCongr (Combinatorics.standardSlotEquiv
            (layout.interactionBlock (Finset.univ : Finset (Fin n)) B)))
          ε β g (evenExternalSubsetTimes times
            (B : Finset (Fin (2 * E))) (layout.evenBlocks B))
      else 0) =
      ∑ d : {d : ExternalInsertionWickDiagram Mode
          ((B : Finset (Fin (2 * E))).card / 2)
          (layout.interactionBlock (Finset.univ : Finset (Fin n)) B).card //
          d.vertexGraph.Preconnected},
        if d.1.externalLabel =
            evenExternalSubsetLabels labels (B : Finset (Fin (2 * E)))
              (layout.evenBlocks B) then
          d.1.dysonAmplitude ε β g
            (evenExternalSubsetTimes times
              (B : Finset (Fin (2 * E))) (layout.evenBlocks B))
        else 0 := by
  classical
  let T := layout.interactionBlock (Finset.univ : Finset (Fin n)) B
  let targetLabels :=
    evenExternalSubsetLabels labels (B : Finset (Fin (2 * E)))
      (layout.evenBlocks B)
  let targetTimes :=
    evenExternalSubsetTimes times (B : Finset (Fin (2 * E)))
      (layout.evenBlocks B)
  have h :=
    ExternalInsertionDiagram.sum_preconnectedSlotCongr
      (E := (B : Finset (Fin (2 * E))).card / 2)
      (N := n) (M := T.card) (T := T)
      (U := (Finset.univ : Finset (Fin T.card)))
      (ExternalLabel := ExternalFieldLabel Mode)
      (InternalLabel := QuarticVertexLabel Mode)
      (Combinatorics.standardSlotEquiv T)
      (fun d : ExternalInsertionWickDiagram Mode
        ((B : Finset (Fin (2 * E))).card / 2) T.card =>
        if d.externalLabel = targetLabels then
          d.dysonAmplitude ε β g targetTimes else 0)
  convert h using 1
  · apply Finset.sum_congr
    · ext d
      simp
    · intro d _
      rfl
  · apply Finset.sum_congr
    · ext d
      simp
    · intro d _
      rfl

open Classical in
/-- For one physical external-component layout, the complete integrated
interaction-shuffle orbit summed over independent connected Wick
families equals the signed product of *standardized consecutive-slot*
local Dyson sums. All interactions are now referred to their blockwise
cardinalities, enabling comparison across distinct physical owner
assignments. This still does not equate a single canonical Dyson
integral with its full shuffle orbit. -/
theorem ExternalInsertionBlockLayout.sum_signedDysonShuffleOrbits_eq_prod_standardized
    {n : ℕ} (layout : ExternalInsertionBlockLayout E n)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (times : Fin (2 * E) → ℝ) :
    (∑ F : layout.ConnectedBlockFamily
        (ExternalLabel := ExternalFieldLabel Mode)
        (InternalLabel := QuarticVertexLabel Mode),
      if ∀ B : layout.partition.parts,
          (F.1 B).externalLabel =
            evenExternalSubsetLabels labels (B : Finset (Fin (2 * E)))
              (layout.evenBlocks B) then
        let d : ExternalInsertionWickDiagram Mode E n :=
          layout.assembleDiagram (Finset.univ : Finset (Fin n)) F.1
        ∑ shuffle : d.ComponentInteractionOrderShuffle,
          d.orderedDysonAmplitude ε β g times
            (d.assembleInteractionOrder d.canonicalComponentInteractionOrders shuffle)
      else 0) =
      externalPartitionSourceSign layout.partition *
        ∏ B : layout.partition.parts,
          ∑ d : {d : ExternalInsertionWickDiagram Mode
              ((B : Finset (Fin (2 * E))).card / 2)
              (layout.interactionBlock (Finset.univ : Finset (Fin n)) B).card //
              d.vertexGraph.Preconnected},
            if d.1.externalLabel =
                evenExternalSubsetLabels labels (B : Finset (Fin (2 * E)))
                  (layout.evenBlocks B) then
              d.1.dysonAmplitude ε β g
                (evenExternalSubsetTimes times
                  (B : Finset (Fin (2 * E))) (layout.evenBlocks B))
            else 0 := by
  classical
  rw [SecondQuantization.Fermionic.ExternalInsertionBlockLayout.sum_signedDysonShuffleOrbits_eq_prod_connectedBlocks
    layout ε β g labels times]
  apply congrArg (fun z : ℂ => externalPartitionSourceSign layout.partition * z)
  apply Finset.prod_congr rfl
  intro B _
  exact SecondQuantization.Fermionic.ExternalInsertionBlockLayout.sum_preconnectedDysonBlock_eq_standardized
    layout B ε β g labels times

omit [LinearOrder Mode] [Fintype Mode] in
/-- On each external-partition block of a vacuum-free diagram, the field
labels used by the source-subset moment are exactly the labels of the
canonical standalone connected-component diagram.

The inverse component/block equivalence is essential here: the statement
does not select an arbitrary representative of a block. -/
theorem evenExternalSubsetLabels_externalPartitionBlock
    {n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (hVac : HasNoVacuumComponent d.vertexGraph)
    (P : (externalComponentPartition d.vertexGraph).parts) :
    HEq
      (evenExternalSubsetLabels d.externalLabel
        (P : Finset (Fin (2 * E)))
        (d.externalComponentPartition_block_card_even P.1 P.2))
      ((d.componentOrderedDiagram
        ((d.vacuumFreeComponentsEquivExternalBlocks hVac).symm P)).externalLabel) := by
  let B := (d.vacuumFreeComponentsEquivExternalBlocks hVac).symm P
  exact (evenExternalSubsetRestriction_heq_of_eq d.externalLabel
    (d.externalComponentPartition_block_card_even P.1 P.2)
    (d.externalSector_card_even B)
    (d.vacuumFreeComponentsEquivExternalBlocks_symm_apply hVac P).symm).trans
      (heq_of_eq (evenExternalSubsetLabels_componentOrderedDiagram (d := d) B))

omit [LinearOrder Mode] [Fintype Mode] in
/-- The same external-block transport preserves the insertion times in
increasing source-slot order, not in the order of their numerical values. -/
theorem evenExternalSubsetTimes_externalPartitionBlock
    {n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (hVac : HasNoVacuumComponent d.vertexGraph)
    (times : Fin (2 * E) → ℝ)
    (P : (externalComponentPartition d.vertexGraph).parts) :
    HEq
      (evenExternalSubsetTimes times
        (P : Finset (Fin (2 * E)))
        (d.externalComponentPartition_block_card_even P.1 P.2))
      (d.componentExternalTime times
        ((d.vacuumFreeComponentsEquivExternalBlocks hVac).symm P)) := by
  let B := (d.vacuumFreeComponentsEquivExternalBlocks hVac).symm P
  exact (evenExternalSubsetRestriction_heq_of_eq times
    (d.externalComponentPartition_block_card_even P.1 P.2)
    (d.externalSector_card_even B)
    (d.vacuumFreeComponentsEquivExternalBlocks_symm_apply hVac P).symm).trans
      (heq_of_eq (evenExternalSubsetTimes_component (d := d) times B))

omit [LinearOrder Mode] in
/-- Explicit finite enumeration of vacuum-free fixed-label diagrams, available
when the target type is mentioned in a theorem statement rather than inside
a `by classical` proof. -/
private noncomputable instance vacuumFreeFixedExternalInsertionWickDiagramFintype
    {K n : ℕ} (labels : Fin (2 * K) → ExternalFieldLabel Mode) :
    Fintype (VacuumFreeFixedExternalInsertionWickDiagram Mode K n labels) := by
  classical
  exact Fintype.ofFinite _

/-- Reindex the actual vacuum-free fixed-label Dyson-diagram coefficient by its
induced external-component partition. The indicator selects precisely the
fiber over each partition; retaining the ambient finite type avoids creating
additional dependent-fiber `Fintype` instances in a theorem statement.

This is a finite reindexing, not yet the connected-component amplitude
factorization or the physical signed partition identity. -/
theorem vacuumFreeExternalInsertionDysonCoefficient_eq_sum_externalPartitionFibers
    {K : ℕ} (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * K) → ExternalFieldLabel Mode)
    (times : Fin (2 * K) → ℝ) (n : ℕ) :
    vacuumFreeExternalInsertionDysonCoefficient ε β g labels times n =
      ∑ π : Finpartition (Finset.univ : Finset (Fin (2 * K))),
        ∑ d : VacuumFreeFixedExternalInsertionWickDiagram Mode K n labels,
          if externalComponentPartition d.1.1.vertexGraph = π then
            d.1.1.dysonAmplitude ε β g times else 0 := by
  classical
  unfold vacuumFreeExternalInsertionDysonCoefficient
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  apply Finset.sum_congr
  · ext d
    simp
  · intro d _
    rfl

/-- A physical vacuum-free Wick diagram can never have an external
connected component with an odd number of fermion insertions. Therefore
the *actual integrated Dyson partition fiber* at an odd-block partition
vanishes term by term, without a cancellation or cumulant assumption. -/
theorem fixedExternalPartitionDysonFiber_eq_zero_of_oddBlock
    {K n : ℕ} (π : Finpartition (Finset.univ : Finset (Fin (2 * K))))
    (B : π.parts) (hodd : ¬ Even (B : Finset (Fin (2 * K))).card)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * K) → ExternalFieldLabel Mode)
    (times : Fin (2 * K) → ℝ) :
    (∑ d : VacuumFreeFixedExternalInsertionWickDiagram Mode K n labels,
      if externalComponentPartition d.1.1.vertexGraph = π then
        d.1.1.dysonAmplitude ε β g times else 0) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro d _
  by_cases hp : externalComponentPartition d.1.1.vertexGraph = π
  · have hmem : (B : Finset (Fin (2 * K))) ∈
        (externalComponentPartition d.1.1.vertexGraph).parts := by
      rw [hp]
      exact B.2
    have hEven := d.1.1.externalComponentPartition_block_card_even B.1 hmem
    exact (hodd hEven).elim
  · simp only [hp, ↓reduceIte]

/-- The **physical** vacuum-free Dyson coefficient is supported only on
external partitions with even block cardinalities. This is the required
fermion-parity reduction *before* the physical fixed-partition layout and
shuffle reindexing; arbitrary odd-block partitions are not silently
discarded. -/
theorem vacuumFreeExternalInsertionDysonCoefficient_eq_sum_evenPartitionFibers
    {K : ℕ} (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * K) → ExternalFieldLabel Mode)
    (times : Fin (2 * K) → ℝ) (n : ℕ) :
    vacuumFreeExternalInsertionDysonCoefficient ε β g labels times n =
      ∑ π : Finpartition (Finset.univ : Finset (Fin (2 * K))),
        if ∀ B : π.parts, Even (B : Finset (Fin (2 * K))).card then
          ∑ d : VacuumFreeFixedExternalInsertionWickDiagram Mode K n labels,
            if externalComponentPartition d.1.1.vertexGraph = π then
              d.1.1.dysonAmplitude ε β g times else 0
        else 0 := by
  classical
  rw [vacuumFreeExternalInsertionDysonCoefficient_eq_sum_externalPartitionFibers]
  apply Finset.sum_congr rfl
  intro π _
  by_cases heven : ∀ B : π.parts, Even (B : Finset (Fin (2 * K))).card
  · simp [heven]
  · have hOdd : ∃ B : π.parts, ¬ Even (B : Finset (Fin (2 * K))).card :=
      not_forall.mp heven
    obtain ⟨B, hBodd⟩ := hOdd
    have hnot : ¬ ∀ P ∈ π.parts, Even P.card := by
      intro h
      exact heven (fun P => h P.1 P.2)
    simpa [hnot] using
      (fixedExternalPartitionDysonFiber_eq_zero_of_oddBlock
        π B hBodd ε β g labels times)

open Classical in
open Classical in
/-- The actual order-`n` vacuum-free Dyson coefficient, with the external
field labels fixed, is an explicit finite sum over all independent
preconnected local external-block diagrams and their interaction-vertex
assignments. The canonical assembly equivalence ensures that each physical
Wick diagram appears exactly once; the external-label indicator excludes
precisely the assembled diagrams with different prescribed insertions.
The shuffle/integral product decomposition is a separate subsequent step. -/
theorem vacuumFreeExternalInsertionDysonCoefficient_eq_sum_connectedBlockFamilies
    {K n : ℕ} (anchor : Fin (2 * K))
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * K) → ExternalFieldLabel Mode)
    (times : Fin (2 * K) → ℝ) :
    vacuumFreeExternalInsertionDysonCoefficient ε β g labels times n =
      ∑ p ∈ ExternalInsertionBlockLayout.connectedAssemblyFiniteDomain
          (E := K) (N := n) (ExternalLabel := ExternalFieldLabel Mode)
          (InternalLabel := QuarticVertexLabel Mode) anchor,
        if (ExternalInsertionBlockLayout.assembleConnectedBlockFamily p).1.externalLabel =
            labels then
          ExternalInsertionWickDiagram.dysonAmplitude
            (ExternalInsertionBlockLayout.assembleConnectedBlockFamily p).1
            ε β g times
        else 0 := by
  classical
  rw [vacuumFreeExternalInsertionDysonCoefficient_eq_sum_if]
  exact ExternalInsertionBlockLayout.sum_vacuumFree_eq_sum_connectedBlockFamilies
    (ExternalLabel := ExternalFieldLabel Mode)
    (InternalLabel := QuarticVertexLabel Mode) anchor
    (fun d : ExternalInsertionWickDiagram Mode K n =>
      if d.externalLabel = labels then d.dysonAmplitude ε β g times else 0)

open Classical in
/-- For a *fixed physical external-component partition*, the actual
fixed-external-label Dyson diagram fiber is reindexed by independent
connected block families with exactly that prescribed source partition.
The external-field-label condition is retained on the assembled diagram;
the integration amplitudes themselves are not yet factorized. -/
theorem sum_fixedExternalPartitionFiber_eq_sum_connectedBlockFamilies
    {K n : ℕ} (anchor : Fin (2 * K))
    (π : Finpartition (Finset.univ : Finset (Fin (2 * K))))
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * K) → ExternalFieldLabel Mode)
    (times : Fin (2 * K) → ℝ) :
    (∑ d : VacuumFreeFixedExternalInsertionWickDiagram Mode K n labels,
      if externalComponentPartition d.1.1.vertexGraph = π then
        d.1.1.dysonAmplitude ε β g times else 0) =
      ∑ p ∈ ExternalInsertionBlockLayout.connectedAssemblyFiniteDomain
          (E := K) (N := n) (ExternalLabel := ExternalFieldLabel Mode)
          (InternalLabel := QuarticVertexLabel Mode) anchor,
        if p.1.partition = π then
          if (ExternalInsertionBlockLayout.assembleConnectedBlockFamily p).1.externalLabel =
              labels then
            ExternalInsertionWickDiagram.dysonAmplitude
              (ExternalInsertionBlockLayout.assembleConnectedBlockFamily p).1
              ε β g times
          else 0
        else 0 := by
  classical
  have hFixed :=
    sum_vacuumFreeFixedExternalInsertionWickDiagram_eq_sum_if
      (Mode := Mode) labels (fun d : ExternalInsertionWickDiagram Mode K n =>
        if externalComponentPartition d.vertexGraph = π then
          d.dysonAmplitude ε β g times else 0)
  calc
    (∑ d : VacuumFreeFixedExternalInsertionWickDiagram Mode K n labels,
      if externalComponentPartition d.1.1.vertexGraph = π then
        d.1.1.dysonAmplitude ε β g times else 0) =
      ∑ d : {d : ExternalInsertionWickDiagram Mode K n //
          HasNoVacuumComponent d.vertexGraph},
        if d.1.externalLabel = labels then
          if externalComponentPartition d.1.vertexGraph = π then
            d.1.dysonAmplitude ε β g times else 0
        else 0 := by
      exact hFixed
    _ = ∑ d : {d : ExternalInsertionWickDiagram Mode K n //
          HasNoVacuumComponent d.vertexGraph},
        if externalComponentPartition d.1.vertexGraph = π then
          if d.1.externalLabel = labels then
            d.1.dysonAmplitude ε β g times else 0
        else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      by_cases hp : externalComponentPartition d.1.vertexGraph = π <;> simp [hp]
    _ = _ :=
      ExternalInsertionBlockLayout.sum_externalPartitionFiber_eq_sum_connectedBlockFamilies
        (ExternalLabel := ExternalFieldLabel Mode)
        (InternalLabel := QuarticVertexLabel Mode) anchor π
        (fun d : ExternalInsertionWickDiagram Mode K n =>
          if d.externalLabel = labels then d.dysonAmplitude ε β g times else 0)

/-- The exact physical fixed-partition Dyson fiber can be enumerated using only
the independently specified local external-source labels. The test of the
*assembled* global label family is equivalent to a separate label test on
every source-partition block. This is needed before summing independently
labelled connected Dyson coefficients, and remains valid for blocks with
no interaction vertices. -/
theorem sum_fixedExternalPartitionFiber_eq_sum_localLabelConnectedBlockFamilies
    {K n : ℕ} (anchor : Fin (2 * K))
    (π : Finpartition (Finset.univ : Finset (Fin (2 * K))))
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * K) → ExternalFieldLabel Mode)
    (times : Fin (2 * K) → ℝ) :
    (∑ d : VacuumFreeFixedExternalInsertionWickDiagram Mode K n labels,
      if externalComponentPartition d.1.1.vertexGraph = π then
        d.1.1.dysonAmplitude ε β g times else 0) =
      ∑ p ∈ ExternalInsertionBlockLayout.connectedAssemblyFiniteDomain
          (E := K) (N := n) (ExternalLabel := ExternalFieldLabel Mode)
          (InternalLabel := QuarticVertexLabel Mode) anchor,
        if p.1.partition = π then
          if ∀ B : p.1.partition.parts,
              (p.2.1 B).externalLabel =
                fun i => labels (p.1.sourceEquiv.symm ⟨B, i⟩) then
            ExternalInsertionWickDiagram.dysonAmplitude
              (ExternalInsertionBlockLayout.assembleConnectedBlockFamily p).1
              ε β g times
          else 0
        else 0 := by
  classical
  rw [sum_fixedExternalPartitionFiber_eq_sum_connectedBlockFamilies
    anchor π ε β g labels times]
  apply Finset.sum_congr rfl
  intro p _
  rcases p with ⟨layout, ⟨F, hconnected⟩⟩
  change
      (if layout.partition = π then
        if (layout.assembleDiagram (Finset.univ : Finset (Fin n)) F).externalLabel =
            labels then
          ExternalInsertionWickDiagram.dysonAmplitude
            (layout.assembleDiagram (Finset.univ : Finset (Fin n)) F)
            ε β g times
        else 0
      else 0) =
      (if layout.partition = π then
        if ∀ B : layout.partition.parts,
            (F B).externalLabel =
              fun i => labels (layout.sourceEquiv.symm ⟨B, i⟩) then
          ExternalInsertionWickDiagram.dysonAmplitude
            (layout.assembleDiagram (Finset.univ : Finset (Fin n)) F)
            ε β g times
        else 0
      else 0)
  simp only [layout.assembleDiagram_externalLabel_eq_iff
    (Finset.univ : Finset (Fin n)) F labels]

/-- The canonical physical Dyson integral of an independently
assembled Wick diagram is precisely the ordered Dyson amplitude for
the block-local orders induced by the increasing ambient order and
the *actual* interaction-assignment shuffle. This identifies the
canonical term among the global order/shuffle terms without asserting
that a single ordered-simplex integral factors over blocks. -/
theorem ExternalInsertionBlockLayout.assembleDiagram_dysonAmplitude_eq_assignmentOrdered
    {n : ℕ} (layout : ExternalInsertionBlockLayout E n)
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram (ExternalFieldLabel Mode) (QuarticVertexLabel Mode)
        ((B : Finset (Fin (2 * E))).card / 2) n
        (layout.interactionBlock (Finset.univ : Finset (Fin n)) B))
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (times : Fin (2 * E) → ℝ) :
    ExternalInsertionWickDiagram.dysonAmplitude
        (layout.assembleDiagram (Finset.univ : Finset (Fin n)) F) ε β g times =
      ExternalInsertionWickDiagram.orderedDysonAmplitude
        (layout.assembleDiagram (Finset.univ : Finset (Fin n)) F) ε β g times
        (layout.interactionOrderDecompositionEquiv.symm
          ((layout.interactionOrderDecompositionEquiv
            ((Finset.univ : Finset (Fin n)).orderIsoOfFin rfl).toEquiv).1,
            layout.interactionAssignmentShuffle)) := by
  let canonical : QuarticVertexOrder (Finset.univ : Finset (Fin n)) :=
    ((Finset.univ : Finset (Fin n)).orderIsoOfFin rfl).toEquiv
  have horder :
      layout.interactionOrderDecompositionEquiv.symm
        ((layout.interactionOrderDecompositionEquiv canonical).1,
          layout.interactionAssignmentShuffle) = canonical := by
    change layout.interactionOrderDecompositionEquiv.symm
      (layout.interactionOrderDecompositionEquiv canonical) = canonical
    exact layout.interactionAssignmentShuffle_reassembles
  rw [horder]
  exact (ExternalInsertionWickDiagram.orderedDysonAmplitude_canonicalOrder
    (layout.assembleDiagram (Finset.univ : Finset (Fin n)) F)
    ε β g times).symm

open Classical in
/-- The actual integrated, fixed-source-label Dyson coefficient in one
even external-component partition is reindexed by the physical interaction
cardinalities and their unique owner shuffle, together with independently
preconnected local labelled Wick diagrams. Each summand remains the
*actual assembled physical Dyson amplitude*; the further shuffle-orbit
summation is needed before its local integrals can be multiplied. -/
theorem sum_fixedExternalPartitionDysonFiber_eq_sizes_shuffles
    {K n : ℕ} (anchor : Fin (2 * K))
    (π : Finpartition (Finset.univ : Finset (Fin (2 * K))))
    (heven : ∀ B : π.parts, Even (B : Finset (Fin (2 * K))).card)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * K) → ExternalFieldLabel Mode)
    (times : Fin (2 * K) → ℝ) :
    (∑ d : VacuumFreeFixedExternalInsertionWickDiagram Mode K n labels,
      if externalComponentPartition d.1.1.vertexGraph = π then
        d.1.1.dysonAmplitude ε β g times else 0) =
      ∑ p ∈ ExternalInsertionBlockLayout.fixedPartitionPhysicalSizeShuffleFiniteDomain
          (E := K) (N := n) (ExternalLabel := ExternalFieldLabel Mode)
          (InternalLabel := QuarticVertexLabel Mode) anchor π heven,
        if (((ExternalInsertionBlockLayout.fixedPartitionPhysicalSizeShuffleEquiv
            (E := K) (N := n) (ExternalLabel := ExternalFieldLabel Mode)
            (InternalLabel := QuarticVertexLabel Mode)
            anchor π heven).symm p).1.1).externalLabel = labels then
          ExternalInsertionWickDiagram.dysonAmplitude
            (((ExternalInsertionBlockLayout.fixedPartitionPhysicalSizeShuffleEquiv
              (E := K) (N := n) (ExternalLabel := ExternalFieldLabel Mode)
              (InternalLabel := QuarticVertexLabel Mode)
              anchor π heven).symm p).1.1) ε β g times
        else 0 := by
  classical
  have hfixed :=
    sum_vacuumFreeFixedExternalInsertionWickDiagram_eq_sum_if
      (Mode := Mode) labels
      (fun d : ExternalInsertionWickDiagram Mode K n =>
        if externalComponentPartition d.vertexGraph = π then
          d.dysonAmplitude ε β g times else 0)
  calc
    (∑ d : VacuumFreeFixedExternalInsertionWickDiagram Mode K n labels,
      if externalComponentPartition d.1.1.vertexGraph = π then
        d.1.1.dysonAmplitude ε β g times else 0) =
      ∑ d : {d : ExternalInsertionWickDiagram Mode K n //
          HasNoVacuumComponent d.vertexGraph},
        if d.1.externalLabel = labels then
          if externalComponentPartition d.1.vertexGraph = π then
            d.1.dysonAmplitude ε β g times else 0
        else 0 := hfixed
    _ = ∑ d : {d : ExternalInsertionWickDiagram Mode K n //
          HasNoVacuumComponent d.vertexGraph},
        if externalComponentPartition d.1.vertexGraph = π then
          if d.1.externalLabel = labels then
            d.1.dysonAmplitude ε β g times else 0
        else 0 := by
          apply Finset.sum_congr rfl
          intro d _
          by_cases hp : externalComponentPartition d.1.vertexGraph = π <;> simp [hp]
    _ = _ :=
      ExternalInsertionBlockLayout.sum_vacuumFree_fixedPartition_eq_sizes_shuffles
        (E := K) (N := n) anchor π heven
        (fun d : ExternalInsertionWickDiagram Mode K n =>
          if d.externalLabel = labels then d.dysonAmplitude ε β g times else 0)

open Classical in
/-- A physical, integrated fixed-label Dyson partition fiber is a finite
sum over the unique owner size/shuffle data and independently connected
local Wick diagrams, with the source-label predicate imposed *blockwise*
in the canonical increasing external-slot order. This is the form needed
to compare the physical owner-shuffle sum with the previously proved
summed connected-block Dyson shuffle orbit. No amplitude has been
factorized at the level of an individual ordered-simplex integral. -/
theorem sum_fixedExternalPartitionDysonFiber_eq_sizes_shuffles_localLabels
    {K n : ℕ} (anchor : Fin (2 * K))
    (π : Finpartition (Finset.univ : Finset (Fin (2 * K))))
    (heven : ∀ B : π.parts, Even (B : Finset (Fin (2 * K))).card)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * K) → ExternalFieldLabel Mode)
    (times : Fin (2 * K) → ℝ) :
    (∑ d : VacuumFreeFixedExternalInsertionWickDiagram Mode K n labels,
      if externalComponentPartition d.1.1.vertexGraph = π then
        d.1.1.dysonAmplitude ε β g times else 0) =
      ∑ p ∈ ExternalInsertionBlockLayout.fixedPartitionPhysicalSizeShuffleFiniteDomain
          (E := K) (N := n) (ExternalLabel := ExternalFieldLabel Mode)
          (InternalLabel := QuarticVertexLabel Mode) anchor π heven,
        let layout : ExternalInsertionBlockLayout K n :=
          ((ExternalInsertionBlockLayout.fixedPartitionSizeShuffleEquiv
            (E := K) (N := n) π heven).symm p.1).1
        if ∀ B : layout.partition.parts,
            (p.2.1 B).externalLabel =
              evenExternalSubsetLabels labels (B : Finset (Fin (2 * K)))
                (layout.evenBlocks B) then
          ExternalInsertionWickDiagram.dysonAmplitude
            (layout.assembleDiagram (Finset.univ : Finset (Fin n)) p.2.1)
            ε β g times
        else 0 := by
  classical
  rw [sum_fixedExternalPartitionDysonFiber_eq_sizes_shuffles
    anchor π heven ε β g labels times]
  apply Finset.sum_congr rfl
  intro p _
  let layout : ExternalInsertionBlockLayout K n :=
    ((ExternalInsertionBlockLayout.fixedPartitionSizeShuffleEquiv
      (E := K) (N := n) π heven).symm p.1).1
  have hd :=
    ExternalInsertionBlockLayout.fixedPartitionPhysicalSizeShuffleEquiv_symm_diagram
      (E := K) (N := n) anchor π heven p
  have hl :=
    ExternalInsertionBlockLayout.assembleDiagram_externalLabel_eq_iff_evenSubsetLabels
      layout p.2.1 labels
  rw [hd]
  exact if_congr hl rfl rfl

open Classical in
/-- At fixed perturbation order and fixed physical external partition,
the genuine vacuum-free Dyson coefficient is a finite sum of *ordered*
Dyson amplitudes indexed by the exact physical owner size/shuffle
assignment. The local source labels are imposed blockwise; each
assembled diagram carries the local interaction orders induced by the
increasing ambient vertex order, rather than any extra permutations.
This is the coefficient-level endpoint of the purely combinatorial
reindexing, before identifying different owner shuffles with a single
physical diagram's full integrated shuffle orbit. -/
theorem sum_fixedExternalPartitionDysonFiber_eq_assignmentOrderedDyson
    {K n : ℕ} (anchor : Fin (2 * K))
    (π : Finpartition (Finset.univ : Finset (Fin (2 * K))))
    (heven : ∀ B : π.parts, Even (B : Finset (Fin (2 * K))).card)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * K) → ExternalFieldLabel Mode)
    (times : Fin (2 * K) → ℝ) :
    (∑ d : VacuumFreeFixedExternalInsertionWickDiagram Mode K n labels,
      if externalComponentPartition d.1.1.vertexGraph = π then
        d.1.1.dysonAmplitude ε β g times else 0) =
      ∑ p ∈ ExternalInsertionBlockLayout.fixedPartitionPhysicalSizeShuffleFiniteDomain
          (E := K) (N := n) (ExternalLabel := ExternalFieldLabel Mode)
          (InternalLabel := QuarticVertexLabel Mode) anchor π heven,
        let layout : ExternalInsertionBlockLayout K n :=
          ((ExternalInsertionBlockLayout.fixedPartitionSizeShuffleEquiv
            (E := K) (N := n) π heven).symm p.1).1
        if ∀ B : layout.partition.parts,
            (p.2.1 B).externalLabel =
              evenExternalSubsetLabels labels (B : Finset (Fin (2 * K)))
                (layout.evenBlocks B) then
          ExternalInsertionWickDiagram.orderedDysonAmplitude
            (layout.assembleDiagram (Finset.univ : Finset (Fin n)) p.2.1)
            ε β g times
            (layout.interactionOrderDecompositionEquiv.symm
              ((layout.interactionOrderDecompositionEquiv
                ((Finset.univ : Finset (Fin n)).orderIsoOfFin rfl).toEquiv).1,
                layout.interactionAssignmentShuffle))
        else 0 := by
  classical
  rw [sum_fixedExternalPartitionDysonFiber_eq_sizes_shuffles_localLabels
    anchor π heven ε β g labels times]
  apply Finset.sum_congr rfl
  intro p _
  let layout : ExternalInsertionBlockLayout K n :=
    ((ExternalInsertionBlockLayout.fixedPartitionSizeShuffleEquiv
      (E := K) (N := n) π heven).symm p.1).1
  have hcanon :=
    ExternalInsertionBlockLayout.assembleDiagram_dysonAmplitude_eq_assignmentOrdered
      layout p.2.1 ε β g times
  exact if_congr Iff.rfl hcanon rfl

/-- The full fixed-order physical Dyson coefficient is reindexed by even
external-component partitions and independently labelled connected blocks.
The owner assignments and genuine assembled Dyson amplitudes are retained:
the remaining factorization must still sum those assignments and their
ordered interaction shuffles. -/
theorem vacuumFreeExternalInsertionDysonCoefficient_eq_sum_evenPartitions_localLabelFamilies
    {K n : ℕ} (anchor : Fin (2 * K))
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * K) → ExternalFieldLabel Mode)
    (times : Fin (2 * K) → ℝ) :
    vacuumFreeExternalInsertionDysonCoefficient ε β g labels times n =
      ∑ π : Finpartition (Finset.univ : Finset (Fin (2 * K))),
        if ∀ B : π.parts, Even (B : Finset (Fin (2 * K))).card then
          ∑ p ∈ ExternalInsertionBlockLayout.connectedAssemblyFiniteDomain
              (E := K) (N := n) (ExternalLabel := ExternalFieldLabel Mode)
              (InternalLabel := QuarticVertexLabel Mode) anchor,
            if p.1.partition = π then
              if ∀ B : p.1.partition.parts,
                  (p.2.1 B).externalLabel =
                    fun i => labels (p.1.sourceEquiv.symm ⟨B, i⟩) then
                ExternalInsertionWickDiagram.dysonAmplitude
                  (ExternalInsertionBlockLayout.assembleConnectedBlockFamily p).1
                  ε β g times
              else 0
            else 0
        else 0 := by
  classical
  rw [vacuumFreeExternalInsertionDysonCoefficient_eq_sum_evenPartitionFibers]
  apply Finset.sum_congr rfl
  intro π _
  by_cases heven : ∀ B : π.parts, Even (B : Finset (Fin (2 * K))).card
  · simpa [heven] using
      (sum_fixedExternalPartitionFiber_eq_sum_localLabelConnectedBlockFamilies
        anchor π ε β g labels times)
  · have hnot : ¬ ∀ P ∈ π.parts, Even P.card := by
      intro h
      exact heven (fun P => h P.1 P.2)
    simp [hnot]

/-- Fully external-connected, vacuum-free Dyson coefficient using the actual
integrated signed Wick diagram amplitude, with all labels and times fixed. -/
noncomputable def connectedExternalInsertionDysonCoefficient {K : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * K) → ExternalFieldLabel Mode)
    (times : Fin (2 * K) → ℝ) (n : ℕ) : ℂ := by
  classical
  exact ∑ d : VacuumFreeFixedExternalInsertionWickDiagram Mode K n labels,
    if AllExternalVerticesConnected d.1.1.vertexGraph then
      d.1.1.dysonAmplitude ε β g times else 0

/-- For any nonempty family of external insertions, the **actual**
fixed-label connected Dyson coefficient is exactly the top external-partition
fiber of the vacuum-free diagram sum.

No quotient by vacuum diagrams or formal cumulant inversion is used here:
connectivity is identified with the genuine graph-induced external partition
of each Wick pairing. -/
theorem connectedExternalInsertionDysonCoefficient_eq_topPartitionFiber
    {K : ℕ} (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * K) → ExternalFieldLabel Mode)
    (times : Fin (2 * K) → ℝ) (n : ℕ)
    (anchor : Fin (2 * K)) :
    connectedExternalInsertionDysonCoefficient ε β g labels times n =
      ∑ d : VacuumFreeFixedExternalInsertionWickDiagram Mode K n labels,
        if externalComponentPartition d.1.1.vertexGraph = ⊤ then
          d.1.1.dysonAmplitude ε β g times else 0 := by
  classical
  unfold connectedExternalInsertionDysonCoefficient
  apply Finset.sum_congr
  · ext d
    simp
  · intro d _
    simp only [← (d.1.1.allExternalVerticesConnected_iff_externalComponentPartition_eq_top anchor)]

/-- The formal Dyson series of the fully external-connected diagram sector.
It is not identified with a source cumulant without the signed moment theorem. -/
noncomputable def connectedExternalInsertionDysonSeries {K : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * K) → ExternalFieldLabel Mode)
    (times : Fin (2 * K) → ℝ) : PowerSeries ℂ :=
  PowerSeries.mk (connectedExternalInsertionDysonCoefficient ε β g labels times)

/-- Physical, vacuum-normalized moment assigned to an external subset.
For odd subsets the operator expectation vanishes by fermion parity; for the
empty subset the normalized moment is one. -/
noncomputable def externalSubsetMomentSeries
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (times : Fin (2 * E) → ℝ)
    (S : Finset (Fin (2 * E))) : PowerSeries ℂ := by
  classical
  if hEmpty : S = ∅ then exact 1
  else if heven : Even S.card then
    exact vacuumFreeExternalInsertionDysonSeries ε β g
      (evenExternalSubsetLabels labels S heven)
      (evenExternalSubsetTimes times S heven)
  else exact 0

/-- The source-subset moment is the vacuum-normalized *physical* vertex-Dyson
correlator for every nonempty even external subset. Multiplication by the
normalized vacuum partition series recovers the operator insertion series.
This bridge uses the existing Gibbs/Wick and Cauchy factorization theorems;
it does not assume the distinct external components are connected. -/
theorem externalSubsetMomentSeries_mul_normalizedPartition_eq_vertexDysonSeries
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (times : Fin (2 * E) → ℝ)
    (S : Finset (Fin (2 * E))) (hS : S ≠ ∅) (heven : Even S.card) :
    externalSubsetMomentSeries ε β g labels times S *
        PowerSeries.normalizeByConstantCoeff
          (Common.dysonTraceSeries (fermionEnergy ε) β (quarticInteraction g)) =
      externalInsertionVertexDysonSeries ε β 0 g
        (evenExternalSubsetLabels labels S heven)
        (evenExternalSubsetTimes times S heven) := by
  have hm : externalSubsetMomentSeries ε β g labels times S =
      vacuumFreeExternalInsertionDysonSeries ε β g
        (evenExternalSubsetLabels labels S heven)
        (evenExternalSubsetTimes times S heven) := by
    simp [externalSubsetMomentSeries, hS, heven]
  rw [hm]
  exact (externalInsertionVertexDysonSeries_eq_vacuumFree_mul_normalizedDysonPartitionSeries
    ε β hβ g (evenExternalSubsetLabels labels S heven)
    (evenExternalSubsetTimes times S heven)).symm

/-- A connected-diagram contribution for each external subset. Odd and empty
subsets contribute zero. This is defined from the actual integrated diagrams,
not by a formal inversion of the moment function. -/
noncomputable def externalSubsetConnectedDiagramSeries
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (times : Fin (2 * E) → ℝ)
    (S : Finset (Fin (2 * E))) : PowerSeries ℂ := by
  classical
  if hEmpty : S = ∅ then exact 0
  else if heven : Even S.card then
    exact connectedExternalInsertionDysonSeries ε β g
      (evenExternalSubsetLabels labels S heven)
      (evenExternalSubsetTimes times S heven)
  else exact 0

/-- The signed partition expansion predicted by the source/cumulant identity,
formed from the actual fully connected diagrammatic contributions.
The remaining Phase 5 theorem must identify this with
`externalSubsetMomentSeries`, coefficientwise at every Dyson order. -/
noncomputable def externalSubsetSignedConnectedMomentSeries
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (times : Fin (2 * E) → ℝ)
    (S : Finset (Fin (2 * E))) : PowerSeries ℂ :=
  Finpartition.weightedMomentFromCumulant
    (fun _ π => PowerSeries.C (externalPartitionSourceSign π))
    (externalSubsetConnectedDiagramSeries ε β g labels times) S

@[simp]
theorem externalSubsetMomentSeries_empty
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (times : Fin (2 * E) → ℝ) :
    externalSubsetMomentSeries ε β g labels times ∅ = 1 := by
  simp [externalSubsetMomentSeries]

@[simp]
theorem externalSubsetConnectedDiagramSeries_empty
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (times : Fin (2 * E) → ℝ) :
    externalSubsetConnectedDiagramSeries ε β g labels times ∅ = 0 := by
  simp [externalSubsetConnectedDiagramSeries]

/-- The signed connected-diagram partition formula has the same
vacuum normalization as the physical subset Dyson moment: it is one at
the empty source set, without assigning an empty connected diagram. -/
@[simp]
theorem externalSubsetSignedConnectedMomentSeries_empty
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (times : Fin (2 * E) → ℝ) :
    externalSubsetSignedConnectedMomentSeries ε β g labels times ∅ = 1 := by
  unfold externalSubsetSignedConnectedMomentSeries
  rw [Finpartition.weightedMomentFromCumulant_empty]
  simp [externalPartitionSourceSign_top]

/-- Odd external subsets carry neither a normalized moment nor a connected
Wick-diagram contribution. -/
theorem externalSubsetSeries_eq_zero_of_odd
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (times : Fin (2 * E) → ℝ)
    (S : Finset (Fin (2 * E))) (hodd : ¬ Even S.card) :
    externalSubsetMomentSeries ε β g labels times S = 0 ∧
      externalSubsetConnectedDiagramSeries ε β g labels times S = 0 := by
  have hne : S ≠ ∅ := by
    intro h
    subst S
    exact hodd (by simp)
  simp [externalSubsetMomentSeries, externalSubsetConnectedDiagramSeries, hne, hodd]


/-- Every partition of an odd-sized external subset contains an odd-sized block.
This makes the odd-fermion vanishing visible directly in the signed source
partition expansion, rather than only in the Wick-diagram definitions. -/
private theorem odd_externalSubset_has_odd_partition_block
    {S : Finset (Fin (2 * E))} (π : Finpartition S)
    (hodd : ¬ Even S.card) :
    ∃ B ∈ π.parts, ¬ Even B.card := by
  classical
  by_contra h
  have hall : ∀ B ∈ π.parts, Even B.card := by
    intro B hB
    by_contra hBodd
    exact h ⟨B, hB, hBodd⟩
  have hsum : ∀ T : Finset (Finset (Fin (2 * E))),
      T ⊆ π.parts → Even (∑ B ∈ T, B.card) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
        intro _
        simp
    | @insert B T hBT ih =>
        intro hsub
        rw [Finset.sum_insert hBT]
        apply Even.add
        · exact hall B (hsub (Finset.mem_insert_self B T))
        · exact ih (Finset.Subset.trans (Finset.subset_insert B T) hsub)
  have hπ := hsum π.parts (Finset.Subset.refl _)
  exact hodd (by simpa only [π.sum_card_parts] using hπ)

/-- The signed connected-partition expression respects fermion parity:
an odd number of source insertions gives zero term by term. No hypothesis
identifying the diagrammatic moments with the partition expression is used. -/
theorem externalSubsetSignedConnectedMomentSeries_eq_zero_of_odd
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (times : Fin (2 * E) → ℝ)
    (S : Finset (Fin (2 * E))) (hodd : ¬ Even S.card) :
    externalSubsetSignedConnectedMomentSeries ε β g labels times S = 0 := by
  classical
  unfold externalSubsetSignedConnectedMomentSeries Finpartition.weightedMomentFromCumulant
  apply Finset.sum_eq_zero
  intro π _
  obtain ⟨B, hB, hBodd⟩ := odd_externalSubset_has_odd_partition_block π hodd
  have hzero : externalSubsetConnectedDiagramSeries ε β g labels times B = 0 :=
    (externalSubsetSeries_eq_zero_of_odd ε β g labels times B hBodd).2
  have hprod : Finpartition.partitionProduct
      (externalSubsetConnectedDiagramSeries ε β g labels times) π = 0 := by
    unfold Finpartition.partitionProduct
    exact Finset.prod_eq_zero hB hzero
  rw [hprod, mul_zero]

/-- Empty and odd external subsets already satisfy the physical
signed partition identity, unconditionally. Thus completing Phase 5
requires proving that identity **only for nonempty even subsets**.

The remaining hypothesis is genuinely diagrammatic: it is not replaced
by an unsigned moment inversion or by defining the connected weights
from the moments. -/
theorem externalSubsetMomentSeries_eq_signedConnected_of_nonempty_even
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (times : Fin (2 * E) → ℝ)
    (hEven : ∀ S : Finset (Fin (2 * E)), S ≠ ∅ → Even S.card →
      externalSubsetMomentSeries ε β g labels times S =
        externalSubsetSignedConnectedMomentSeries ε β g labels times S) :
    ∀ S : Finset (Fin (2 * E)),
      externalSubsetMomentSeries ε β g labels times S =
        externalSubsetSignedConnectedMomentSeries ε β g labels times S := by
  intro S
  by_cases hEmpty : S = ∅
  · subst S
    simp
  · by_cases hParity : Even S.card
    · exact hEven S hEmpty hParity
    · rw [(externalSubsetSeries_eq_zero_of_odd ε β g labels times S hParity).1,
        externalSubsetSignedConnectedMomentSeries_eq_zero_of_odd
          ε β g labels times S hParity]

/-- The precise remaining physical bridge for Phase 5: once the actual
vacuum-normalized Wick/Dyson moments satisfy the signed external-partition
identity, the recursively defined fermionic *source cumulant* is the fully
externally connected integrated diagram sum.

This theorem uses genuine signed moment inversion; it does not assume
unsigned Möbius inversion or conflate vacuum-freeness with connectivity.
Its hypothesis is the still-required diagram-assembly/shuffle identity. -/
theorem externalSubsetSourceCumulantSeries_eq_connectedDiagramSeries_of_signedMoments
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (times : Fin (2 * E) → ℝ)
    (hDiagram : ∀ S : Finset (Fin (2 * E)),
      externalSubsetMomentSeries ε β g labels times S =
        externalSubsetSignedConnectedMomentSeries ε β g labels times S) :
    externalSubsetSourceCumulantSeries
        (externalSubsetMomentSeries ε β g labels times) =
      externalSubsetConnectedDiagramSeries ε β g labels times := by
  apply externalPartitionWeightedMoment_injective
  · simp
  · intro S
    calc
      Finpartition.weightedMomentFromCumulant
          (fun _ π => PowerSeries.C (externalPartitionSourceSign π))
          (externalSubsetSourceCumulantSeries
            (externalSubsetMomentSeries ε β g labels times)) S =
        externalSubsetMomentSeries ε β g labels times S :=
          externalSubsetSourceCumulantSeries_reconstruct
            (externalSubsetMomentSeries ε β g labels times) (by simp) S
      _ = Finpartition.weightedMomentFromCumulant
          (fun _ π => PowerSeries.C (externalPartitionSourceSign π))
          (externalSubsetConnectedDiagramSeries ε β g labels times) S := hDiagram S


end Fermionic
end SecondQuantization
