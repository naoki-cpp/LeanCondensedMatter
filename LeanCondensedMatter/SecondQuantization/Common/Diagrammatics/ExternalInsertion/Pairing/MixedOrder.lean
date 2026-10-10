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

/-- Transport a diagram pairing from fixed flattened-leg order to mixed-time atomic order. -/
noncomputable def ExternalInsertionDiagram.pairingInMixedOrder {E n : ℕ}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E n (Finset.univ : Finset (Fin n)))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    Pairing (2 * n + E) :=
  d.pairing.transport (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ)

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
  unfold ExternalInsertionDiagram.pairingInMixedOrder
    externalInsertionMixedTimeAmbientPositionEquiv
  rw [externalInsertionStandardToMixedAtomicPositionEquiv_eq_of_orderSignature_eq
    externalTime σ υ h]

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
  change (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ)
      ((d.pairing.transport (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ)).partner p) =
    d.pairing.partner (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ p)
  rw [PairingOn.transport_partner]
  exact (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ).apply_symm_apply _


end Common
end SecondQuantization
