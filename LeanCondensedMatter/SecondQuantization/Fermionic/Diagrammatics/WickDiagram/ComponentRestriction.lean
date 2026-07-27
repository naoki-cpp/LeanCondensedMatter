import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ComponentRestriction
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentPartition

set_option linter.style.header false

/-!
# Fermionic component restriction

This module specializes the label-generic quartic-diagram restriction construction to fermionic
quartic vertex labels while preserving the existing public API.
-/

namespace SecondQuantization

variable {Mode : Type*} {N : ℕ}

noncomputable section

def QuarticWickDiagram.legInBlock {S : Finset (Fin N)}
    (_d : QuarticWickDiagram Mode N S) (B : Finset (Fin N))
    (leg : Fin (2 * (2 * S.card))) : Prop :=
  (vertexOfLeg leg : Fin N) ∈ B

theorem QuarticWickDiagram.componentBlock_eq_iff_mem {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) (v : ↥S) :
    d.componentBlock v = B ↔ (v : Fin N) ∈ B :=
  Common.QuarticDiagram.componentBlock_eq_iff_mem d hB v

theorem QuarticWickDiagram.componentPart_subset {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) : B ⊆ S :=
  Common.QuarticDiagram.componentPart_subset d hB

theorem QuarticWickDiagram.componentBlock_vertexOfLeg_partner {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (leg : Fin (2 * (2 * S.card))) :
    d.componentBlock (vertexOfLeg (d.pairing.partner leg)) =
      d.componentBlock (vertexOfLeg leg) :=
  Common.QuarticDiagram.componentBlock_vertexOfLeg_partner d leg

theorem QuarticWickDiagram.legInBlock_partner_iff {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) (leg : Fin (2 * (2 * S.card))) :
    d.legInBlock B leg ↔ d.legInBlock B (d.pairing.partner leg) :=
  Common.QuarticDiagram.legInBlock_partner_iff d hB leg

abbrev QuarticWickDiagram.restrictedPartner {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) :
    Equiv.Perm {leg : Fin (2 * (2 * S.card)) // d.legInBlock B leg} :=
  Common.QuarticDiagram.restrictedPartner d hB

theorem QuarticWickDiagram.restrictedPartner_val {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts)
    (leg : {leg : Fin (2 * (2 * S.card)) // d.legInBlock B leg}) :
    (d.restrictedPartner hB leg : Fin (2 * (2 * S.card))) = d.pairing.partner leg :=
  Common.QuarticDiagram.restrictedPartner_val d hB leg

theorem QuarticWickDiagram.restrictedPartner_involutive {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) :
    Function.Involutive (d.restrictedPartner hB) :=
  Common.QuarticDiagram.restrictedPartner_involutive d hB

theorem QuarticWickDiagram.restrictedPartner_ne_self {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts)
    (leg : {leg : Fin (2 * (2 * S.card)) // d.legInBlock B leg}) :
    d.restrictedPartner hB leg ≠ leg :=
  Common.QuarticDiagram.restrictedPartner_ne_self d hB leg

abbrev QuarticWickDiagram.subtypeMemBlockEquiv {S : Finset (Fin N)}
    (B : Finset (Fin N)) (hBS : B ⊆ S) : {v : ↥S // (v : Fin N) ∈ B} ≃ ↥B :=
  Common.QuarticDiagram.subtypeMemBlockEquiv B hBS

@[simp]
theorem QuarticWickDiagram.subtypeMemBlockEquiv_symm_val {S : Finset (Fin N)}
    {B : Finset (Fin N)} (hBS : B ⊆ S) (v : ↥B) :
    (((QuarticWickDiagram.subtypeMemBlockEquiv B hBS).symm v :
      {v : ↥S // (v : Fin N) ∈ B}) : Fin N) = (v : Fin N) :=
  Common.QuarticDiagram.subtypeMemBlockEquiv_symm_val hBS v

theorem QuarticWickDiagram.legOfVertexLocal_vertexOfLeg_localLegOfLeg
    {S : Finset (Fin N)} (leg : Fin (2 * (2 * S.card))) :
    legOfVertexLocal (vertexOfLeg leg) (localLegOfLeg leg) = leg :=
  Common.QuarticDiagram.legOfVertexLocal_vertexOfLeg_localLegOfLeg leg

abbrev QuarticWickDiagram.blockLegEquiv {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) :
    {leg : Fin (2 * (2 * S.card)) // d.legInBlock B leg} ≃ Fin (2 * (2 * B.card)) :=
  Common.QuarticDiagram.blockLegEquiv d hB

theorem QuarticWickDiagram.vertexOfLeg_blockLegEquiv {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts)
    (leg : {leg : Fin (2 * (2 * S.card)) // d.legInBlock B leg}) :
    vertexOfLeg (d.blockLegEquiv hB leg) =
      QuarticWickDiagram.subtypeMemBlockEquiv B (d.componentPart_subset hB)
        ⟨vertexOfLeg (leg : Fin (2 * (2 * S.card))), leg.2⟩ :=
  Common.QuarticDiagram.vertexOfLeg_blockLegEquiv d hB leg

theorem QuarticWickDiagram.localLegOfLeg_blockLegEquiv {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts)
    (leg : {leg : Fin (2 * (2 * S.card)) // d.legInBlock B leg}) :
    localLegOfLeg (d.blockLegEquiv hB leg) =
      localLegOfLeg (leg : Fin (2 * (2 * S.card))) :=
  Common.QuarticDiagram.localLegOfLeg_blockLegEquiv d hB leg

abbrev QuarticWickDiagram.restrictedPairing {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) :
    Common.BlochDeDominicis.Pairing (2 * B.card) :=
  Common.QuarticDiagram.restrictedPairing d hB

theorem QuarticWickDiagram.restrictedPairing_partner_blockLegEquiv {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts)
    (leg : {leg : Fin (2 * (2 * S.card)) // d.legInBlock B leg}) :
    (d.restrictedPairing hB).partner (d.blockLegEquiv hB leg) =
      d.blockLegEquiv hB (d.restrictedPartner hB leg) :=
  Common.QuarticDiagram.restrictedPairing_partner_blockLegEquiv d hB leg

abbrev QuarticWickDiagram.restrictComponent {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) : QuarticWickDiagram Mode N B :=
  Common.QuarticDiagram.restrictComponent d hB

theorem QuarticWickDiagram.restrictComponent_pairing {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) :
    (d.restrictComponent hB).pairing = d.restrictedPairing hB :=
  Common.QuarticDiagram.restrictComponent_pairing d hB

end

end SecondQuantization
