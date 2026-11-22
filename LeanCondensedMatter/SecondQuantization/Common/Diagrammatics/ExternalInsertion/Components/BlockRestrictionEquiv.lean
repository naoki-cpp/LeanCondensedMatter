import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.PhysicalComponentPairing

set_option linter.style.header false

/-!
# Restriction and equivalence for block-respecting diagrams

Injectivity, inverse restriction, equivalence with block-local diagrams, and
exact finite reindexing with or without prescribed external labels.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {E N : ℕ}

/-- Connected local blocks also ensure that no internal-only vacuum
component survives the assembly. Each prescribed partition part is
nonempty and therefore supplies an external vertex reachable from all
its assigned interaction vertices. -/
theorem ExternalInsertionBlockLayout.hasNoVacuumComponent_assembleDiagram
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B))
    (hconnected : ∀ B, (F B).vertexGraph.Preconnected) :
    HasNoVacuumComponent (layout.assembleDiagram S F).vertexGraph := by
  intro v
  let B : layout.partition.parts := (layout.interactionEquiv S v).1
  have hnonempty : (B : Finset (Fin (2 * E))).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (layout.partition.ne_bot B.2)
  obtain ⟨e, he⟩ := hnonempty
  refine ⟨e, ?_⟩
  apply (layout.assembleDiagram_reachable_iff_same_block S F hconnected
    (Sum.inl e) (Sum.inr v)).2
  have hsource : (layout.sourceEquiv e).1 = B := by
    apply Subtype.ext
    simpa only [layout.sourceEquiv_fst] using
      (layout.partition.part_eq_of_mem B.2 he)
  simpa only [layout.vertexEquiv_external, layout.vertexEquiv_interaction] using
    hsource

/-- Independent block assembly is **injective on the complete labelled
diagram data**: all local external labels, interaction labels and pairing
partners can be recovered from the assembled diagram.

This is the essential inverse-information statement for arbitrary external
partitions, separate from the remaining proof that connected local diagrams
produce exactly the prescribed graph component partition. -/
theorem ExternalInsertionBlockLayout.assembleDiagram_injective
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N)) :
    Function.Injective (layout.assembleDiagram (ExternalLabel := ExternalLabel)
      (InternalLabel := InternalLabel) S) := by
  intro F G h
  funext B
  apply ExternalInsertionDiagram.ext
  · funext e
    have he := congrArg (fun d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S =>
      d.externalLabel (layout.sourceEquiv.symm ⟨B, e⟩)) h
    simpa only [layout.assembleDiagram_externalLabel] using he
  · funext v
    have hv := congrArg (fun d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S =>
      d.vertexLabel ((layout.interactionEquiv S).symm ⟨B, v⟩)) h
    simpa only [layout.assembleDiagram_vertexLabel] using hv
  · apply Combinatorics.PairingOn.ext
    apply Equiv.ext
    intro p
    have hp := congrArg (fun d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S =>
      d.pairing.partner ((layout.legEquiv S).symm ⟨B, p⟩)) h
    simp only [layout.assembleDiagram_partner] at hp
    have hpair := (layout.legEquiv S).symm.injective hp
    exact eq_of_heq (Sigma.mk.inj_iff.mp hpair).2



/-- A pairing whose partners stay in their prescribed external blocks
also preserves the dependent sigma index after transport by the concrete
flattened-leg equivalence. -/
private theorem ExternalInsertionBlockLayout.pairingTransport_preserves_block
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (hblock : ∀ leg,
      (layout.legEquiv S (d.pairing.partner leg)).1 =
        (layout.legEquiv S leg).1) :
    ∀ x, ((d.pairing.transport (layout.legEquiv S).symm).partner x).1 = x.1 := by
  intro x
  have hx := hblock ((layout.legEquiv S).symm x)
  simpa only [PairingOn.transport_partner, Equiv.symm_symm,
    Equiv.apply_symm_apply] using hx

/-- Extract a labelled local diagram from a physical pairing respecting a
prescribed independent-block layout. Local external slots and interaction
vertices retain their original ambient identities and order; the local
pairing is obtained by restricting the transported ambient involution. -/
noncomputable def ExternalInsertionBlockLayout.restrictBlock
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (hblock : ∀ leg,
      (layout.legEquiv S (d.pairing.partner leg)).1 =
        (layout.legEquiv S leg).1)
    (B : layout.partition.parts) :
    ExternalInsertionDiagram ExternalLabel InternalLabel
      ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B) where
  externalLabel e := d.externalLabel (layout.sourceEquiv.symm ⟨B, e⟩)
  vertexLabel v := d.vertexLabel ((layout.interactionEquiv S).symm ⟨B, v⟩)
  pairing := (d.pairing.transport (layout.legEquiv S).symm).sigmaFiberPairing
    (layout.pairingTransport_preserves_block S d hblock) B

/-- Reassembly of all restricted labelled blocks recovers exactly the
original physical diagram, including every label and pairing partner. -/
theorem ExternalInsertionBlockLayout.assembleDiagram_restrictBlock
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (hblock : ∀ leg,
      (layout.legEquiv S (d.pairing.partner leg)).1 =
        (layout.legEquiv S leg).1) :
    layout.assembleDiagram S (layout.restrictBlock S d hblock) = d := by
  apply ExternalInsertionDiagram.ext
  · funext e
    change d.externalLabel (layout.sourceEquiv.symm (layout.sourceEquiv e)) =
      d.externalLabel e
    rw [Equiv.symm_apply_apply]
  · funext v
    change d.vertexLabel ((layout.interactionEquiv S).symm
      (layout.interactionEquiv S v)) = d.vertexLabel v
    rw [Equiv.symm_apply_apply]
  · change
      (PairingOn.sigmaCongrRight (fun B =>
        (d.pairing.transport (layout.legEquiv S).symm).sigmaFiberPairing
          (layout.pairingTransport_preserves_block S d hblock) B)).transport
        (layout.legEquiv S) = d.pairing
    rw [PairingOn.sigmaCongrRight_sigmaFiberPairing,
      PairingOn.transport_transport_symm]

/-- Restriction is also a left inverse of independent assembly, without
a connectedness hypothesis: the assembled pairing respects every assigned
block, and injectivity of assembly recovers all local diagram data. -/
theorem ExternalInsertionBlockLayout.restrictBlock_assembleDiagram
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B)) :
    (fun B => layout.restrictBlock S (layout.assembleDiagram S F)
      (layout.assembleDiagram_partner_block S F) B) = F := by
  apply layout.assembleDiagram_injective S
  exact layout.assembleDiagram_restrictBlock S
    (layout.assembleDiagram S F) (layout.assembleDiagram_partner_block S F)


/-- The complete family of block-local labelled pairings is equivalent
to the global labelled diagrams whose propagators respect the prescribed
external-block layout. Both sides retain every external/interaction label
and every pairing partner. -/
noncomputable def ExternalInsertionBlockLayout.assemblyEquivBlockRespecting
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N)) :
    (∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B)) ≃
    {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S //
      ∀ leg, (layout.legEquiv S (d.pairing.partner leg)).1 =
        (layout.legEquiv S leg).1} where
  toFun F := ⟨layout.assembleDiagram S F, layout.assembleDiagram_partner_block S F⟩
  invFun d := layout.restrictBlock S d.1 d.2
  left_inv F := layout.restrictBlock_assembleDiagram S F
  right_inv d := by
    apply Subtype.ext
    exact layout.assembleDiagram_restrictBlock S d.1 d.2

/-- The block-assembly equivalence recovers the *exact* original physical
diagram from the inverse image, rather than only its connected partition. -/
@[simp]
theorem ExternalInsertionBlockLayout.assemblyEquivBlockRespecting_apply
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B)) :
    (layout.assemblyEquivBlockRespecting S F).1 = layout.assembleDiagram S F :=
  rfl

/-- Reindex *any* finite weighted sum of block-respecting physical
diagrams by their independent local labelled diagrams. This is the
diagram-pairing sum conversion underlying fixed-order Dyson-fiber sums;
the integrand can be the physical integrated amplitude itself. -/
theorem ExternalInsertionBlockLayout.sum_blockRespecting_eq_sum_local
    {ExternalLabel InternalLabel M : Type*}
    [Fintype ExternalLabel] [Fintype InternalLabel] [AddCommMonoid M]
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (weight : ExternalInsertionDiagram ExternalLabel InternalLabel E N S → M) :
    (∑ d : {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S //
        ∀ leg, (layout.legEquiv S (d.pairing.partner leg)).1 =
          (layout.legEquiv S leg).1}, weight d.1) =
      ∑ F : ∀ B : layout.partition.parts,
          ExternalInsertionDiagram ExternalLabel InternalLabel
            ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B),
        weight (layout.assembleDiagram S F) := by
  classical
  simpa only [layout.assemblyEquivBlockRespecting_apply] using
    (Equiv.sum_comp (layout.assemblyEquivBlockRespecting S)
      (fun d => weight d.1)).symm

/-- The assembled diagram has prescribed external field labels exactly
when every local block carries the induced increasing-order restriction
of those labels. No relative ordering of the numerical times is used. -/
theorem ExternalInsertionBlockLayout.assembleDiagram_externalLabel_eq_iff
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B))
    (labels : Fin (2 * E) → ExternalLabel) :
    (layout.assembleDiagram S F).externalLabel = labels ↔
      ∀ B : layout.partition.parts,
        (F B).externalLabel =
          fun i => labels (layout.sourceEquiv.symm ⟨B, i⟩) := by
  constructor
  · intro h B
    funext i
    rw [← layout.assembleDiagram_externalLabel S F B i]
    exact congrFun h (layout.sourceEquiv.symm ⟨B, i⟩)
  · intro h
    funext e
    have he := congrFun (h (layout.sourceEquiv e).1)
      (layout.sourceEquiv e).2
    change (F (layout.sourceEquiv e).1).externalLabel
      (layout.sourceEquiv e).2 = labels e
    change (F (layout.sourceEquiv e).1).externalLabel
      (layout.sourceEquiv e).2 =
        labels (layout.sourceEquiv.symm (layout.sourceEquiv e)) at he
    simpa only [Equiv.symm_apply_apply] using he

/-- Blockwise assembly remains an exact equivalence after *fixing* the
external field labels. Only internal vertex labels and the Wick pairing
are allowed to vary in each finite Dyson coefficient. -/
noncomputable def ExternalInsertionBlockLayout.assemblyEquivBlockRespectingFixedLabels
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (labels : Fin (2 * E) → ExternalLabel) :
    {F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B) //
      ∀ B : layout.partition.parts,
        (F B).externalLabel =
          fun i => labels (layout.sourceEquiv.symm ⟨B, i⟩)} ≃
    {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S //
      (∀ leg, (layout.legEquiv S (d.pairing.partner leg)).1 =
        (layout.legEquiv S leg).1) ∧ d.externalLabel = labels} where
  toFun F :=
    ⟨layout.assembleDiagram S F.1,
      layout.assembleDiagram_partner_block S F.1,
      (layout.assembleDiagram_externalLabel_eq_iff S F.1 labels).2 F.2⟩
  invFun d :=
    ⟨layout.restrictBlock S d.1 d.2.1,
      (layout.assembleDiagram_externalLabel_eq_iff S
        (layout.restrictBlock S d.1 d.2.1) labels).1 (by
          rw [layout.assembleDiagram_restrictBlock S d.1 d.2.1]
          exact d.2.2)⟩
  left_inv F := by
    apply Subtype.ext
    exact layout.restrictBlock_assembleDiagram S F.1
  right_inv d := by
    apply Subtype.ext
    exact layout.assembleDiagram_restrictBlock S d.1 d.2.1

/-- The fixed-label equivalence preserves the assembled diagram itself. -/
@[simp]
theorem ExternalInsertionBlockLayout.assemblyEquivBlockRespectingFixedLabels_apply
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (labels : Fin (2 * E) → ExternalLabel)
    (F : {F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B) //
      ∀ B : layout.partition.parts,
        (F B).externalLabel =
          fun i => labels (layout.sourceEquiv.symm ⟨B, i⟩)}) :
    (layout.assemblyEquivBlockRespectingFixedLabels S labels F).1 =
      layout.assembleDiagram S F.1 := rfl

open Classical in
/-- Finite weighted fixed-external-label diagram sums can be reindexed
over independently chosen local labels and pairings with those exact
external field labels. In particular, the weight may be the integrated
Dyson amplitude at one fixed perturbative order. -/
theorem ExternalInsertionBlockLayout.sum_blockRespectingFixedLabels_eq_sum_local
    {ExternalLabel InternalLabel M : Type*}
    [Fintype ExternalLabel] [Fintype InternalLabel] [AddCommMonoid M]
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N))
    (labels : Fin (2 * E) → ExternalLabel)
    (weight : ExternalInsertionDiagram ExternalLabel InternalLabel E N S → M) :
    (∑ d : {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S //
      (∀ leg, (layout.legEquiv S (d.pairing.partner leg)).1 =
        (layout.legEquiv S leg).1) ∧ d.externalLabel = labels}, weight d.1) =
    ∑ F : {F : ∀ B : layout.partition.parts,
        ExternalInsertionDiagram ExternalLabel InternalLabel
          ((B : Finset (Fin (2 * E))).card / 2) N (layout.interactionBlock S B) //
      ∀ B : layout.partition.parts,
        (F B).externalLabel =
          fun i => labels (layout.sourceEquiv.symm ⟨B, i⟩)},
        weight (layout.assembleDiagram S F.1) := by
  classical
  simpa only [layout.assemblyEquivBlockRespectingFixedLabels_apply] using
    (Equiv.sum_comp (layout.assemblyEquivBlockRespectingFixedLabels S labels)
      (fun d => weight d.1)).symm

end Common
end SecondQuantization
