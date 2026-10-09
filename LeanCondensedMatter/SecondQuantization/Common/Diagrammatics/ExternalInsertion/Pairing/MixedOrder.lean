import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Core.Diagram
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.MixedOrderSignature
import LeanCondensedMatter.Combinatorics.PerfectPairing.Transport

set_option linter.style.header false

/-!
# Mixed-order pairing transport for external-insertion diagrams

The pairing of any diagram whose internal slots are the full finite slot family can be transported
from fixed flattened-leg positions to mixed-time atomic positions. This construction and its partner
coherence depend only on the diagram pairing and the generic mixed-order position equivalence.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*}

/-- Cast the pairing cardinality from the `Finset.univ` representation to the explicit slot count. -/
private noncomputable def externalInsertionPairingCastEquiv (E n : ℕ) :
    Pairing (2 * (Finset.univ : Finset (Fin n)).card + E) ≃ Pairing (2 * n + E) :=
  Equiv.cast (by simp)

/-- Transport a diagram pairing from fixed flattened-leg order to mixed-time atomic order. -/
noncomputable def ExternalInsertionDiagram.pairingInMixedOrder {E n : ℕ}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E n (Finset.univ : Finset (Fin n)))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    Pairing (2 * n + E) :=
  (externalInsertionPairingCastEquiv E n d.pairing).transport
    (externalInsertionStandardToMixedAtomicPositionEquiv externalTime σ).symm

/-- The mixed pairing is constant on each finite external-insertion order-signature
fiber. This statement concerns only pairing transport; the time-dependent contraction kernel
is not constant on those fibers. -/
theorem ExternalInsertionDiagram.pairingInMixedOrder_eq_of_orderSignature_eq
    {E n : ℕ}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E n
      (Finset.univ : Finset (Fin n)))
    (externalTime : Fin (2 * E) → ℝ) (σ υ : Fin n → ℝ)
    (h : externalInsertionOrderSignature externalTime σ =
      externalInsertionOrderSignature externalTime υ) :
    d.pairingInMixedOrder externalTime σ =
      d.pairingInMixedOrder externalTime υ := by
  have hpos : externalInsertionStandardToMixedAtomicPositionEquiv externalTime σ =
      externalInsertionStandardToMixedAtomicPositionEquiv externalTime υ := by
    unfold externalInsertionStandardToMixedAtomicPositionEquiv
    rw [externalInsertionMixedTimeOrderedAtomicLegEquiv_eq_of_orderSignature_eq
      externalTime σ υ h]
  unfold ExternalInsertionDiagram.pairingInMixedOrder
  rw [hpos]

private theorem externalInsertionPairingCastEquiv_partner {E n : ℕ}
    (pairing : Pairing (2 * (Finset.univ : Finset (Fin n)).card + E))
    (p : Fin (2 * (2 * n + E))) :
    (finCongr (by simp)) ((externalInsertionPairingCastEquiv E n pairing).partner p) =
      pairing.partner ((finCongr (by simp)) p) := by
  let h : 2 * (Finset.univ : Finset (Fin n)).card + E = 2 * n + E := by
    simp
  have hcast : externalInsertionPairingCastEquiv E n pairing =
      Equiv.cast (congrArg Pairing h) pairing := by
    unfold externalInsertionPairingCastEquiv
    congr
  have hfin : (finCongr (by simp) :
      Fin (2 * (2 * n + E)) ≃
        Fin (2 * (2 * (Finset.univ : Finset (Fin n)).card + E))) =
      finCongr (congrArg (fun k : ℕ => 2 * k) h.symm) := by
    congr
  rw [hcast, hfin]
  exact pairing.cast_partner h p

/-- Transporting a mixed-order partner back to the fixed flattened enumeration recovers the
original diagram partner. -/
theorem ExternalInsertionDiagram.mixedTimeAmbientPositionEquiv_partner {E n : ℕ}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E n (Finset.univ : Finset (Fin n)))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (p : Fin (2 * (2 * n + E))) :
    externalInsertionMixedTimeAmbientPositionEquiv externalTime σ
        ((d.pairingInMixedOrder externalTime σ).partner p) =
      d.pairing.partner
        (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ p) := by
  change (finCongr (by simp))
      ((externalInsertionStandardToMixedAtomicPositionEquiv externalTime σ).symm
        (((externalInsertionPairingCastEquiv E n d.pairing).transport
          (externalInsertionStandardToMixedAtomicPositionEquiv externalTime σ).symm).partner p)) =
    d.pairing.partner
      ((finCongr (by simp))
        ((externalInsertionStandardToMixedAtomicPositionEquiv externalTime σ).symm p))
  rw [PairingOn.transport_partner]
  simp only [Equiv.symm_symm]
  rw [(externalInsertionStandardToMixedAtomicPositionEquiv externalTime σ).symm_apply_apply]
  exact externalInsertionPairingCastEquiv_partner d.pairing
    ((externalInsertionStandardToMixedAtomicPositionEquiv externalTime σ).symm p)


end Common
end SecondQuantization
