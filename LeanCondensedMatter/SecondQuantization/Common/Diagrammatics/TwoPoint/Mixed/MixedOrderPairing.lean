import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedComponentPosition
import LeanCondensedMatter.Combinatorics.PerfectPairing.Relabel

set_option linter.style.header false

/-!
# Mixed-order pairing for generic two-point diagrams

This module owns the statistics-independent transport of a two-point diagram pairing from the
standard external-plus-interaction leg enumeration to the mixed imaginary-time atomic enumeration.
The mixed-position coordinate system itself is owned by `MixedComponentPosition`.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

/-- Cast the standard diagram pairing cardinality from `univ.card` to the explicit slot count. -/
noncomputable def orderedTwoPointPairingCastEquiv (n : ℕ) :
    Pairing (2 * (Finset.univ : Finset (Fin n)).card + 1) ≃ Pairing (2 * n + 1) :=
  Equiv.cast (by simp)

/-- A generic two-point diagram pairing transported into mixed-time atomic order. -/
noncomputable def TwoPointDiagram.pairingInMixedOrder
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) : Pairing (2 * n + 1) :=
  (orderedTwoPointPairingCastEquiv n d.pairing).relabel
    (standardToMixedAtomicPositionEquiv τ τ' σ).symm

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

/-- Transporting a mixed-order partner back to the standard diagram enumeration recovers the
original generic diagram partner. -/
theorem TwoPointDiagram.mixedTimeAmbientPositionEquiv_partner
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (p : Fin (2 * (2 * n + 1))) :
    mixedTimeAmbientPositionEquiv τ τ' σ
        ((d.pairingInMixedOrder τ τ' σ).partner p) =
      d.pairing.partner (mixedTimeAmbientPositionEquiv τ τ' σ p) := by
  change (finCongr (by simp))
      ((standardToMixedAtomicPositionEquiv τ τ' σ).symm
        (((orderedTwoPointPairingCastEquiv n d.pairing).relabel
          (standardToMixedAtomicPositionEquiv τ τ' σ).symm).partner p)) =
    d.pairing.partner
      ((finCongr (by simp))
        ((standardToMixedAtomicPositionEquiv τ τ' σ).symm p))
  rw [Pairing.relabel_partner]
  simp only [Equiv.symm_symm]
  rw [(standardToMixedAtomicPositionEquiv τ τ' σ).symm_apply_apply]
  exact orderedTwoPointPairingCastEquiv_partner d.pairing
    ((standardToMixedAtomicPositionEquiv τ τ' σ).symm p)

/-- The diagram pairing as a map on atomic leg identities; this map is independent of the mixed-time
enumeration. -/
noncomputable def TwoPointDiagram.atomicLegPartner
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (leg : OrderedTwoPointLeg n) : OrderedTwoPointLeg n :=
  twoPointLegEquiv (Finset.univ : Finset (Fin n))
    (d.pairing.partner
      ((twoPointLegEquiv (Finset.univ : Finset (Fin n))).symm leg))

/-- The mixed-order partner is the time-independent leg partner conjugated by the mixed enumeration. -/
theorem TwoPointDiagram.pairingInMixedOrder_partner_eq_atomicLegPartner
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (p : Fin (2 * (2 * n + 1))) :
    (d.pairingInMixedOrder τ τ' σ).partner p =
      mixedTimeOrderedAtomicLegPosition τ τ' σ
        (d.atomicLegPartner (mixedTimeOrderedAtomicLegEquiv τ τ' σ p)) := by
  apply (mixedTimeOrderedAtomicLegEquiv τ τ' σ).injective
  rw [mixedTimeOrderedAtomicLegEquiv_mixedTimeOrderedAtomicLegPosition,
    ← twoPointLegEquiv_mixedTimeAmbientPositionEquiv,
    ← twoPointLegEquiv_mixedTimeAmbientPositionEquiv,
    d.mixedTimeAmbientPositionEquiv_partner]
  rw [TwoPointDiagram.atomicLegPartner,
    (twoPointLegEquiv (Finset.univ : Finset (Fin n))).symm_apply_apply]

/-- The mixed-order partner of the position selected by a leg identity is the position selected by
the partner leg. -/
theorem TwoPointDiagram.pairingInMixedOrder_partner_legPosition
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (leg : OrderedTwoPointLeg n) :
    (d.pairingInMixedOrder τ τ' σ).partner
        (mixedTimeOrderedAtomicLegPosition τ τ' σ leg) =
      mixedTimeOrderedAtomicLegPosition τ τ' σ (d.atomicLegPartner leg) := by
  rw [d.pairingInMixedOrder_partner_eq_atomicLegPartner,
    mixedTimeOrderedAtomicLegEquiv_mixedTimeOrderedAtomicLegPosition]

end Common
end SecondQuantization
