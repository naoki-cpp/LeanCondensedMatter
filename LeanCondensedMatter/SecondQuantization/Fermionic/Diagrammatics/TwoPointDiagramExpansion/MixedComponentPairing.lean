import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Reindexing
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.MixedComponentPosition
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ExternalSlotSplit

set_option linter.style.header false

/-!
# Mixed-time two-point pairing by full components

Common owns the mixed component-position fibers and their standard component-leg coordinates. This
module adds the pairing-specific transport for fixed-external fermionic two-point Wick diagrams: the
mixed-order partner preserves the Common component assignment and restricts to the external or vacuum
component pairings.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*}

/-- Casting the number of pairs transports the partner permutation through the corresponding cast
of flattened positions. -/
private theorem pairingCast_partner {m n : ℕ} (h : m = n)
    (pairing : Pairing m) (p : Fin (2 * n)) :
    (finCongr (congrArg (fun k : ℕ => 2 * k) h.symm))
        ((Equiv.cast (congrArg Pairing h) pairing).partner p) =
      pairing.partner
        ((finCongr (congrArg (fun k : ℕ => 2 * k) h.symm)) p) := by
  subst n
  rfl

/-- The slot-count cast of a pairing intertwines partners with the corresponding cast of positions. -/
private theorem orderedTwoPointPairingCastEquiv_partner {n : ℕ}
    (pairing : Pairing (2 * (Finset.univ : Finset (Fin n)).card + 1))
    (p : Fin (2 * (2 * n + 1))) :
    (finCongr (by simp)) ((orderedTwoPointPairingCastEquiv n pairing).partner p) =
      pairing.partner ((finCongr (by simp)) p) := by
  let h : 2 * (Finset.univ : Finset (Fin n)).card + 1 = 2 * n + 1 := by
    simp
  have hcast : orderedTwoPointPairingCastEquiv n pairing =
      Equiv.cast (congrArg Pairing h) pairing := by
    unfold orderedTwoPointPairingCastEquiv
    congr
  have hfin : (finCongr (by simp) :
      Fin (2 * (2 * n + 1)) ≃
        Fin (2 * (2 * (Finset.univ : Finset (Fin n)).card + 1))) =
      finCongr (congrArg (fun k : ℕ => 2 * k) h.symm) := by
    congr
  rw [hcast, hfin]
  exact pairingCast_partner h pairing p

/-- Transporting the mixed-order partner back to the standard diagram enumeration recovers the
ambient diagram partner. -/
theorem FixedExternalTwoPointWickDiagram.mixedTimeAmbientPositionEquiv_partner
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ) (p : Fin (2 * (2 * n + 1))) :
    mixedTimeAmbientPositionEquiv τ τ' σ
        ((d.pairingInMixedOrder τ τ' σ).partner p) =
      d.1.pairing.partner (mixedTimeAmbientPositionEquiv τ τ' σ p) := by
  change (finCongr (by simp))
      ((standardToMixedAtomicPositionEquiv τ τ' σ).symm
        (((orderedTwoPointPairingCastEquiv n d.1.pairing).relabel
          (standardToMixedAtomicPositionEquiv τ τ' σ).symm).partner p)) =
    d.1.pairing.partner
      ((finCongr (by simp))
        ((standardToMixedAtomicPositionEquiv τ τ' σ).symm p))
  rw [Pairing.relabel_partner]
  simp only [Equiv.symm_symm]
  rw [(standardToMixedAtomicPositionEquiv τ τ' σ).symm_apply_apply]
  exact orderedTwoPointPairingCastEquiv_partner d.1.pairing
    ((standardToMixedAtomicPositionEquiv τ τ' σ).symm p)

/-- The mixed-order pairing partner remains in the same full component. -/
@[simp]
theorem FixedExternalTwoPointWickDiagram.mixedPositionComponent_partner
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ) (p : Fin (2 * (2 * n + 1))) :
    d.1.mixedPositionComponent τ τ' σ
        ((d.pairingInMixedOrder τ τ' σ).partner p) =
      d.1.mixedPositionComponent τ τ' σ p := by
  apply Subtype.ext
  change d.1.componentBlock
      (Common.twoPointVertexOfLeg
        (mixedTimeAmbientPositionEquiv τ τ' σ
          ((d.pairingInMixedOrder τ τ' σ).partner p))) =
    d.1.componentBlock
      (Common.twoPointVertexOfLeg (mixedTimeAmbientPositionEquiv τ τ' σ p))
  rw [d.mixedTimeAmbientPositionEquiv_partner]
  exact d.1.componentBlock_vertexOfLeg_partner _

/-- The mixed-order partner restricted to one full component-position fiber. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedRestrictedPartner
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.1.componentPartition.parts) :
    Equiv.Perm (d.1.MixedComponentPosition τ τ' σ B) :=
  (d.pairingInMixedOrder τ τ' σ).partner.subtypePerm fun p => by
    rw [d.mixedPositionComponent_partner]

/-- The restricted mixed partner has the ambient mixed position as its underlying value. -/
theorem FixedExternalTwoPointWickDiagram.mixedRestrictedPartner_val
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.1.componentPartition.parts)
    (p : d.1.MixedComponentPosition τ τ' σ B) :
    (d.mixedRestrictedPartner τ τ' σ B p : Fin (2 * (2 * n + 1))) =
      (d.pairingInMixedOrder τ τ' σ).partner p :=
  congrArg Subtype.val (Equiv.Perm.subtypePerm_apply _ _ p)

/-- The mixed component-position equivalence intertwines the mixed restricted partner with the
standard component restricted partner. -/
@[simp]
theorem FixedExternalTwoPointWickDiagram.mixedComponentPositionEquiv_partner
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.1.componentPartition.parts)
    (p : d.1.MixedComponentPosition τ τ' σ B) :
    d.1.mixedComponentPositionEquiv τ τ' σ B
        (d.mixedRestrictedPartner τ τ' σ B p) =
      d.1.restrictedPartner (B : Finset (Common.TwoPointVertex
        (Finset.univ : Finset (Fin n))))
        (d.1.mixedComponentPositionEquiv τ τ' σ B p) := by
  apply Subtype.ext
  change mixedTimeAmbientPositionEquiv τ τ' σ
      (d.mixedRestrictedPartner τ τ' σ B p) =
    (d.1.restrictedPartner (B : Finset (Common.TwoPointVertex
      (Finset.univ : Finset (Fin n))))
      (d.1.mixedComponentPositionEquiv τ τ' σ B p) :
        Fin (2 * (2 * (Finset.univ : Finset (Fin n)).card + 1)))
  rw [d.mixedRestrictedPartner_val, d.mixedTimeAmbientPositionEquiv_partner,
    d.1.restrictedPartner_val]
  apply congrArg d.1.pairing.partner
  rfl

/-- The canonical external split pairing partner is the transport of the mixed restricted partner. -/
theorem FixedExternalTwoPointWickDiagram.externalVacuumSplit_fst_partner_mixedExternalPositionEquiv
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (p : d.1.MixedComponentPosition τ τ' σ d.1.externalComponentPart) :
    d.1.externalVacuumSplit.1.pairing.partner
        (d.1.mixedExternalPositionEquiv τ τ' σ p) =
      d.1.mixedExternalPositionEquiv τ τ' σ
        (d.mixedRestrictedPartner τ τ' σ d.1.externalComponentPart p) := by
  change d.1.externalVacuumSplit.1.pairing.partner
      (d.1.externalComponentLegEquiv.symm
        (d.1.mixedComponentPositionEquiv τ τ' σ d.1.externalComponentPart p)) =
    d.1.externalComponentLegEquiv.symm
      (d.1.mixedComponentPositionEquiv τ τ' σ d.1.externalComponentPart
        (d.mixedRestrictedPartner τ τ' σ d.1.externalComponentPart p))
  rw [← d.1.externalComponentLegEquiv_symm_restrictedPartner,
    d.mixedComponentPositionEquiv_partner]

/-- A vacuum restricted pairing partner is the transport of the corresponding mixed restricted
partner. -/
theorem FixedExternalTwoPointWickDiagram.restrictedVacuumPairing_partner_mixedVacuumPositionEquiv
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.1.componentPartition.parts)
    (hVac : d.1.ComponentIsVacuum B)
    (p : d.1.MixedComponentPosition τ τ' σ B) :
    (d.1.restrictedVacuumPairing B hVac).partner
        (d.1.mixedVacuumPositionEquiv τ τ' σ B hVac p) =
      d.1.mixedVacuumPositionEquiv τ τ' σ B hVac
        (d.mixedRestrictedPartner τ τ' σ B p) := by
  change (d.1.restrictedVacuumPairing B hVac).partner
      (d.1.vacuumBlockLegEquiv B hVac
        (d.1.mixedComponentPositionEquiv τ τ' σ B p)) =
    d.1.vacuumBlockLegEquiv B hVac
      (d.1.mixedComponentPositionEquiv τ τ' σ B
        (d.mixedRestrictedPartner τ τ' σ B p))
  rw [d.1.restrictedVacuumPairing_partner_vacuumBlockLegEquiv,
    d.mixedComponentPositionEquiv_partner]

end Fermionic
end SecondQuantization
