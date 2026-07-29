import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentPairing

set_option linter.style.header false

/-!
# Component-local normalized pair sets

The component ordered-leg embedding is strictly monotone and intertwines pairing partners. Therefore
it preserves the normalized orientation used by `Pairing.pairs`, not merely the underlying unordered
partner orbit.
-/

namespace SecondQuantization

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
  constructor
  · rintro ⟨hab, hpartner⟩
    have hmono := d.componentOrderedLeg_strictMono shuffle B
    have habLocal : a < b := by
      apply lt_of_not_ge
      intro hba
      exact (not_lt_of_ge (hmono.monotone hba)) hab
    refine ⟨habLocal, ?_⟩
    apply d.componentOrderedLeg_injective shuffle B
    calc
      d.componentOrderedLeg shuffle B
          (((d.restrictComponent B.2).pairingInOrder (orders B)).partner a) =
        (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).partner
          (d.componentOrderedLeg shuffle B a) :=
        (d.pairingInOrder_partner_componentOrderedLeg orders shuffle B a).symm
      _ = d.componentOrderedLeg shuffle B b := hpartner
  · rintro ⟨hab, hpartner⟩
    refine ⟨d.componentOrderedLeg_strictMono shuffle B hab, ?_⟩
    rw [d.pairingInOrder_partner_componentOrderedLeg orders shuffle B, hpartner]

end SecondQuantization
