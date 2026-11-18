import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ExternalSourceCumulant
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.InteractionPictureVertexDyson
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ComponentIntegral
import Mathlib.Data.Fintype.EquivFin
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.ExternalConnectivity

set_option linter.style.header false

/-!
# External-subset component assembly and Dyson block identities

Identify the canonical increasing order of external field subsets with the
source labels and times of connected components. Compare assembled blocks
with their physical component restrictions and transport signed Dyson
shuffle-orbit amplitudes before passing to fixed-label diagram sums.
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
  exact (heq_of_eq
    (ExternalInsertionBlockLayout.assembleDiagram_externalLabel_eq_evenExternalSubsetLabels
      layout F B)).trans
    ((evenExternalSubsetRestriction_heq_of_eq d.externalLabel
      (layout.evenBlocks B) (d.externalSector_card_even C)
      (layout.assembleDiagram_componentExternalSector_external
        (Finset.univ : Finset (Fin n)) F hconnected e).symm).trans
      (heq_of_eq (evenExternalSubsetLabels_componentOrderedDiagram (d := d) C)))

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
  let d := layout.assembleDiagram (Finset.univ : Finset (Fin n)) F
  let B := (layout.sourceEquiv e).1
  let C : d.vertexGraph.componentPartition.parts :=
    ⟨d.vertexGraph.componentBlock (Sum.inl e),
      d.vertexGraph.componentBlock_mem_componentPartition (Sum.inl e)⟩
  have hlocal :
      (fun i : Fin (2 * (B.1.card / 2)) =>
        times (layout.sourceEquiv.symm ⟨B, i⟩)) =
        evenExternalSubsetTimes times (B : Finset (Fin (2 * E)))
          (layout.evenBlocks B) := by
    funext i
    exact congrArg times (layout.sourceEquiv_symm_apply B i)
  exact (heq_of_eq hlocal).trans
    ((evenExternalSubsetRestriction_heq_of_eq times
      (layout.evenBlocks B) (d.externalSector_card_even C)
      (layout.assembleDiagram_componentExternalSector_external
        (Finset.univ : Finset (Fin n)) F hconnected e).symm).trans
      (heq_of_eq (evenExternalSubsetTimes_component (d := d) times C)))

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
  have hself : P.transport (Equiv.refl _) = P := by
    apply Combinatorics.PairingOn.ext
    apply Equiv.ext
    intro i
    simp only [Combinatorics.PairingOn.transport_partner, Equiv.refl_apply,
      Equiv.refl_symm]
  exact heq_of_eq (by
    simpa only [finCongr_refl, Equiv.refl_symm, hself] using hpair)

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
  have hsector : T = layout.interactionBlock S B :=
    layout.assembleDiagram_componentInteractionSector_external S F hconnected e
  have hcount : d.externalPairCount C = B.1.card / 2 :=
    layout.assembleDiagram_componentExternalPairCount_external S F hconnected e
  have hcards : 2 * T.card + d.externalPairCount C =
      2 * (layout.interactionBlock S B).card + B.1.card / 2 := by
    rw [hsector, hcount]
  have hpair :
      (d.restrictComponent C).pairing.transport
        (finCongr (congrArg (fun k : ℕ => 2 * k) hcards)).symm =
      (F B).pairing := by
    have hp := layout.physicalComponentCanonicalPairing_eq_local S F hconnected e
    change (d.restrictComponent C).pairing.transport
      ((d.componentBlockLegEquiv C).symm.trans
        (layout.physicalComponentLegEquiv S F hconnected e)).symm =
      (F B).pairing at hp
    rw [layout.physicalComponentCanonicalLegEquiv_eq_finCongr S F hconnected e] at hp
    exact hp
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
        (layout.interactionBlock S B))) :=
    (heq_of_eq (d.componentOrderedDiagram_eq_slotCongr C)).trans
      (externalInsertionSlotCongr_heq_of_diagram_heq
        hcount hsector (d.restrictComponent C) (F B) hphysical)
  have htimes : HEq (d.componentExternalTime externalTime C)
      (fun i : Fin (2 * (B.1.card / 2)) =>
        externalTime (layout.sourceEquiv.symm ⟨B, i⟩)) :=
    (ExternalInsertionBlockLayout.assembleDiagram_componentExternalTime_eq_localTimes
      layout F hconnected externalTime e).symm
  congr 1 <;> first
    | exact congrArg Finset.card hsector
    | exact hcount
    | exact hordered
    | exact htimes

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
    Equiv.subtypeEquiv (Equiv.refl _) (fun _ => by simp only [Equiv.refl_apply, hpart])
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
    obtain ⟨e, -, he⟩ := layout.partition.part_surjOn B.2
    have hsource : (layout.sourceEquiv e).1 = B :=
      Subtype.ext ((layout.sourceEquiv_fst e).trans he)
    have hC :
        reindex.symm B =
          ⟨d.vertexGraph.componentBlock (Sum.inl e),
            d.vertexGraph.componentBlock_mem_componentPartition (Sum.inl e)⟩ := by
      apply reindex.injective
      apply Subtype.ext
      rw [Equiv.apply_symm_apply, hblock]
      exact (congrArg Subtype.val hsource.symm).trans
        (layout.assembleDiagram_componentExternalSector_external S F hconnected e).symm
    rw [hC]
    have h := ExternalInsertionBlockLayout.assembleConnectedBlocks_componentDysonAmplitude_eq_local
      layout F hconnected ε β g externalTime e
    rw [hsource] at h
    simpa only [d, S] using h
  have horbit := ExternalInsertionBlockLayout.assembleConnectedBlocks_signedDysonShuffleOrbit
    layout F hconnected ε β g externalTime
  exact horbit.trans
    (congrArg (fun z : ℂ => externalPartitionSourceSign layout.partition * z)
      ((Equiv.prod_comp reindex.symm
        (fun C : d.vertexGraph.componentPartition.parts =>
          ExternalInsertionWickDiagram.dysonAmplitude
            (d.componentOrderedDiagram C) ε β g
            (d.componentExternalTime externalTime C))).symm.trans
        (Finset.prod_congr rfl (fun B _ => hlocal B))))

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
  exact layout.assembleDiagram_externalLabel_eq_iff
    (Finset.univ : Finset (Fin n)) F labels

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
  exact ExternalInsertionBlockLayout.assembleConnectedBlocks_signedDysonShuffleOrbit_eq_independentLocals
    layout F hconnected ε β g times

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
      simpa only [mul_ite, mul_zero] using
        (if_congr Iff.rfl (horbit F) rfl)
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
  all_goals
    apply Finset.sum_congr
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


end Fermionic
end SecondQuantization
