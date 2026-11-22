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
  have hsrc : HEq (d.restrictComponent C).externalLabel (F B).externalLabel := by
    have hlocal :
        (F B).externalLabel =
          evenExternalSubsetLabels d.externalLabel
            (B : Finset (Fin (2 * E))) (layout.evenBlocks B) := by
      funext i
      simpa only [evenExternalSubsetLabels, evenExternalSubsetOrderIso,
        layout.sourceEquiv_symm_apply] using
        (layout.assembleDiagram_externalLabel S F B i).symm
    have hlabels :
        HEq (F B).externalLabel (d.componentOrderedDiagram C).externalLabel :=
      (heq_of_eq hlocal).trans
        ((evenExternalSubsetRestriction_heq_of_eq d.externalLabel
          (layout.evenBlocks B) (d.externalSector_card_even C)
          (layout.assembleDiagram_componentExternalSector_external S F hconnected e).symm).trans
          (heq_of_eq rfl))
    exact hlabels.symm
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
        externalTime (layout.sourceEquiv.symm ⟨B, i⟩)) := by
    have hlocal :
        (fun i : Fin (2 * (B.1.card / 2)) =>
          externalTime (layout.sourceEquiv.symm ⟨B, i⟩)) =
          evenExternalSubsetTimes externalTime (B : Finset (Fin (2 * E)))
            (layout.evenBlocks B) := by
      funext i
      exact congrArg externalTime (layout.sourceEquiv_symm_apply B i)
    exact ((heq_of_eq hlocal).trans
      ((evenExternalSubsetRestriction_heq_of_eq externalTime
        (layout.evenBlocks B) (d.externalSector_card_even C)
        (layout.assembleDiagram_componentExternalSector_external S F hconnected e).symm).trans
        (heq_of_eq rfl))).symm
  congr 1
  exact congrArg Finset.card hsector

/-- The complete physical component-shuffle orbit of assembled connected
Wick blocks equals the source-partition Koszul sign times the product of
independent local Dyson amplitudes at canonically restricted subset times.

Each local factor retains its actual labels, oriented pairing, and increasing
interaction-slot order. Only the complete shuffle sum factors, not an
individual ordered-simplex integral. -/
theorem ExternalInsertionBlockLayout.assembleConnectedBlocks_signedDysonShuffleOrbit_eq_subsetTimes
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
            ε β g (evenExternalSubsetTimes externalTime
              (B : Finset (Fin (2 * E))) (layout.evenBlocks B)) := by
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

open Classical in
/-- At one *actual physical* external-block layout, integrating over
all increasing interaction-owner shuffles factors the genuinely
assembled Wick diagram into its connected Dyson blocks. The global
Dyson orders are actual owner relabelings, identified pointwise with
the graph-component orders; no individual canonical simplex is
declared permutation-invariant. -/
theorem ExternalInsertionBlockLayout.sum_assignmentOwnerShuffle_eq_signedProduct
    {n : ℕ} (layout : ExternalInsertionBlockLayout E n)
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram (ExternalFieldLabel Mode) (QuarticVertexLabel Mode)
        ((B : Finset (Fin (2 * E))).card / 2) n
        (layout.interactionBlock (Finset.univ : Finset (Fin n)) B))
    (hconnected : ∀ B, (F B).vertexGraph.Preconnected)
    (anchor : Fin (2 * E))
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) :
    let d : ExternalInsertionWickDiagram Mode E n :=
      layout.assembleDiagram (Finset.univ : Finset (Fin n)) F
    (∑ τ : Combinatorics.FamilySlotShuffleTo
        (fun B : layout.partition.parts =>
          (layout.interactionBlock (Finset.univ : Finset (Fin n)) B).card)
        (Finset.univ : Finset (Fin n)).card,
      d.orderedDysonAmplitude ε β g externalTime
        ((layout.interactionAssignmentShuffle.ambientRelabel τ).symm.trans
          ((Finset.univ : Finset (Fin n)).orderIsoOfFin rfl).toEquiv)) =
      externalPartitionSourceSign layout.partition *
        ∏ B : layout.partition.parts,
          ExternalInsertionWickDiagram.dysonAmplitude
            ((F B).slotCongr (Combinatorics.standardSlotEquiv
              (layout.interactionBlock (Finset.univ : Finset (Fin n)) B)))
            ε β g (evenExternalSubsetTimes externalTime
              (B : Finset (Fin (2 * E))) (layout.evenBlocks B)) := by
  classical
  let d : ExternalInsertionWickDiagram Mode E n :=
    layout.assembleDiagram (Finset.univ : Finset (Fin n)) F
  let hVac : HasNoVacuumComponent d.vertexGraph :=
    layout.hasNoVacuumComponent_assembleDiagram
      (Finset.univ : Finset (Fin n)) F hconnected
  have hLayout : d.externalBlockLayout hVac anchor = layout :=
    layout.externalBlockLayout_assembleDiagram_eq F hconnected anchor
  have hOrbit := d.sum_physicalOwnerShuffle_orderedDysonAmplitude_eq_componentOrbit
    hVac anchor ε β g externalTime
  rw [hLayout] at hOrbit
  exact hOrbit.trans
    (layout.assembleConnectedBlocks_signedDysonShuffleOrbit_eq_subsetTimes
      F hconnected ε β g externalTime)

open Classical in
/-- At one fixed physical owner assignment, summing all genuine
transported-order Dyson amplitudes over the independent owner
shuffles is exactly the signed product of connected local Dyson
amplitudes. The reference owner assignment is arbitrary; the proof
reindexes the *entire finite orbit* through the actual graph-component
shuffle rather than declaring any canonical integral invariant. -/
theorem ExternalInsertionBlockLayout.ofFamilyShuffle_signedDysonOwnerOrbit_eq_prod
    {n : ℕ}
    (π : Finpartition (Finset.univ : Finset (Fin (2 * E))))
    (heven : ∀ B : π.parts, Even (B : Finset (Fin (2 * E))).card)
    {size : π.parts → ℕ}
    (σ : Combinatorics.FamilySlotShuffleTo size n)
    (F : (ExternalInsertionBlockLayout.ofFamilyShuffle π heven σ).ConnectedBlockFamily
      (ExternalLabel := ExternalFieldLabel Mode)
      (InternalLabel := QuarticVertexLabel Mode))
    (anchor : Fin (2 * E))
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) :
    let layout := ExternalInsertionBlockLayout.ofFamilyShuffle π heven σ
    let d : ExternalInsertionWickDiagram Mode E n :=
      layout.assembleDiagram (Finset.univ : Finset (Fin n)) F.1
    (∑ τ : Combinatorics.FamilySlotShuffleTo size n,
      d.orderedDysonAmplitude ε β g externalTime
        (((Finset.univ : Finset (Fin n)).orderIsoOfFin rfl).toEquiv.trans
          (fullInteractionSlotEquiv (σ.ambientRelabel τ)).symm)) =
      externalPartitionSourceSign π *
        ∏ B : π.parts,
          ExternalInsertionWickDiagram.dysonAmplitude
            ((F.1 B).slotCongr (Combinatorics.standardSlotEquiv
              (layout.interactionBlock (Finset.univ : Finset (Fin n)) B)))
            ε β g (evenExternalSubsetTimes externalTime
              (B : Finset (Fin (2 * E))) (heven B)) := by
  classical
  let layout := ExternalInsertionBlockLayout.ofFamilyShuffle π heven σ
  let d : ExternalInsertionWickDiagram Mode E n :=
    layout.assembleDiagram (Finset.univ : Finset (Fin n)) F.1
  let e := ExternalInsertionBlockLayout.ofFamilyShuffle_ownerShuffleEquiv π heven σ
  let w : Combinatorics.FamilySlotShuffleTo
      (fun B : π.parts =>
        (layout.interactionBlock (Finset.univ : Finset (Fin n)) B).card)
      (Finset.univ : Finset (Fin n)).card → ℂ :=
    fun ρ => d.orderedDysonAmplitude ε β g externalTime
      ((layout.interactionAssignmentShuffle.ambientRelabel ρ).symm.trans
        ((Finset.univ : Finset (Fin n)).orderIsoOfFin rfl).toEquiv)
  calc
    _ = ∑ τ : Combinatorics.FamilySlotShuffleTo size n, w (e τ) := by
      apply Finset.sum_congr rfl
      intro τ _
      exact congrArg (d.orderedDysonAmplitude ε β g externalTime)
        (ExternalInsertionBlockLayout.ofFamilyShuffle_ownerOrderedDysonOrder
          π heven σ τ).symm
    _ = ∑ ρ, w ρ := Equiv.sum_comp e w
    _ = _ := layout.sum_assignmentOwnerShuffle_eq_signedProduct
      F.1 F.2 anchor ε β g externalTime

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
      simpa only [condition, weight, mul_ite, mul_zero] using
        (if_congr Iff.rfl
          (ExternalInsertionBlockLayout.assembleConnectedBlocks_signedDysonShuffleOrbit_eq_subsetTimes
            layout F.1 F.2 ε β g times) rfl)
    _ = externalPartitionSourceSign layout.partition *
        ∏ B : layout.partition.parts,
          ∑ d : {d : ExternalInsertionDiagram
              (ExternalFieldLabel Mode) (QuarticVertexLabel Mode)
              ((B : Finset (Fin (2 * E))).card / 2) n
              (layout.interactionBlock (Finset.univ : Finset (Fin n)) B) //
                d.vertexGraph.Preconnected},
            if condition B d.1 then weight B d.1 else 0 := by
      simpa only [condition, weight] using
        (congrArg (fun z : ℂ => externalPartitionSourceSign layout.partition * z)
          (layout.sum_connectedBlockFamilies_prod_if condition weight))
    _ = _ := by
      apply congrArg (fun z : ℂ => externalPartitionSourceSign layout.partition * z)
      apply Finset.prod_congr rfl
      intro B _
      simpa only [condition, weight] using
        (ExternalInsertionBlockLayout.sum_preconnectedDysonBlock_eq_standardized
          layout B ε β g labels times)

open Classical in
/-- For the fixed-size standardized owner-shuffle family, imposing the
external source labels on the *actual assembled Wick diagram* is
equivalent to imposing them on every standardized connected block.
In particular, the label indicator is independent of the owner
shuffle and cannot produce an additional multiplicity. -/
theorem ExternalInsertionBlockLayout.standardizedOwnerFamily_externalLabel_iff
    {n : ℕ}
    (π : Finpartition (Finset.univ : Finset (Fin (2 * E))))
    (heven : ∀ B : π.parts, Even (B : Finset (Fin (2 * E))).card)
    {size : π.parts → ℕ}
    (σ : Combinatorics.FamilySlotShuffleTo size n)
    (Q : ∀ B : π.parts,
      {d : ExternalInsertionWickDiagram Mode
          ((B : Finset (Fin (2 * E))).card / 2) (size B) //
        d.vertexGraph.Preconnected})
    (labels : Fin (2 * E) → ExternalFieldLabel Mode) :
    let layout := ExternalInsertionBlockLayout.ofFamilyShuffle π heven σ
    let F := (ExternalInsertionBlockLayout.ofFamilyShuffleFixedSizeStandardizedFamilyEquiv
      (ExternalLabel := ExternalFieldLabel Mode)
      (InternalLabel := QuarticVertexLabel Mode) π heven σ).symm Q
    (layout.assembleDiagram (Finset.univ : Finset (Fin n)) F.1).externalLabel =
        labels ↔
      ∀ B : π.parts,
        (Q B).1.externalLabel =
          evenExternalSubsetLabels labels (B : Finset (Fin (2 * E))) (heven B) := by
  classical
  let layout := ExternalInsertionBlockLayout.ofFamilyShuffle π heven σ
  let e := ExternalInsertionBlockLayout.ofFamilyShuffleFixedSizeStandardizedFamilyEquiv
    (ExternalLabel := ExternalFieldLabel Mode)
    (InternalLabel := QuarticVertexLabel Mode) π heven σ
  let F := e.symm Q
  have hQ (B : π.parts) :
      (Q B).1.externalLabel = (F.1 B).externalLabel := by
    have h :=
      congrArg (fun G => (G B).1.externalLabel) (e.apply_symm_apply Q)
    change (F.1 B).externalLabel = (Q B).1.externalLabel at h
    exact h.symm
  change (layout.assembleDiagram (Finset.univ : Finset (Fin n)) F.1).externalLabel =
      labels ↔ _
  rw [layout.assembleDiagram_externalLabel_eq_iff
    (Finset.univ : Finset (Fin n)) F.1 labels]
  constructor
  · intro h B
    rw [hQ B]
    simpa only [evenExternalSubsetLabels, evenExternalSubsetOrderIso,
      layout.sourceEquiv_symm_apply] using h B
  · intro h B
    rw [← hQ B]
    simpa only [evenExternalSubsetLabels, evenExternalSubsetOrderIso,
      layout.sourceEquiv_symm_apply] using h B

end Fermionic
end SecondQuantization
