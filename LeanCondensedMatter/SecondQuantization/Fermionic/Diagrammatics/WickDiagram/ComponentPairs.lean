import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentPairing

set_option linter.style.header false

/-!
# Component-local normalized pair sets

The component ordered-leg embedding is strictly monotone and intertwines pairing partners. Therefore
it preserves the normalized orientation used by `Pairing.pairs`, not merely the underlying unordered
partner orbit.
-/

namespace SecondQuantization

open Combinatorics

variable {Mode : Type*} {N : ℕ}

/-- A component-local normalized pair maps to, and is reflected by, the corresponding normalized
pair of the assembled global ordered pairing. -/
theorem QuarticWickDiagram.mem_pairingInOrder_pairs_componentOrderedLeg_iff
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts)
    (a b : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    (d.componentOrderedLeg shuffle B a, d.componentOrderedLeg shuffle B b) ∈
        (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).pairs ↔
      (a, b) ∈ ((d.restrictComponent B.2).pairingInOrder (orders B)).pairs := by
  rw [Common.BlochDeDominicis.Pairing.mem_pairs_iff,
    Common.BlochDeDominicis.Pairing.mem_pairs_iff]
  let e := d.componentOrderedLegOrderEmbedding shuffle B
  constructor
  · rintro ⟨hab, hpartner⟩
    refine ⟨e.lt_iff_lt.mp hab, ?_⟩
    apply e.injective
    calc
      d.componentOrderedLeg shuffle B
          (((d.restrictComponent B.2).pairingInOrder (orders B)).partner a) =
        (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).partner
          (d.componentOrderedLeg shuffle B a) :=
        (d.pairingInOrder_partner_componentOrderedLeg orders shuffle B a).symm
      _ = d.componentOrderedLeg shuffle B b := hpartner
  · rintro ⟨hab, hpartner⟩
    refine ⟨e.lt_iff_lt.mpr hab, ?_⟩
    rw [d.pairingInOrder_partner_componentOrderedLeg orders shuffle B, hpartner]

end SecondQuantization
