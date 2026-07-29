import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentCrossing
import LeanCondensedMatter.Combinatorics.PerfectPairing.PairEndpoints
import LeanCondensedMatter.Combinatorics.PerfectPairing.CrossingParity

set_option linter.style.header false

/-!
# Endpoint inversion parity for pairs in distinct components

Pairs transported from different connected components are distinct normalized pairs of the assembled
global pairing. Their endpoints are therefore disjoint, so the generic endpoint-inversion parity
criterion applies directly.
-/

namespace SecondQuantization

variable {Mode : Type*} {N : ℕ}

/-- A pair from component `B` and a pair from a distinct component `C` cross geometrically exactly
when their four cross-pair endpoint comparisons have odd parity. -/
theorem QuarticWickDiagram.componentPairEndpointInversionCount_mod_two_eq_one_iff_crosses
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B C : d.componentPartition.parts) (hBC : B ≠ C)
    (p : d.LocalOrderedPair orders B) (q : d.LocalOrderedPair orders C) :
    Common.BlochDeDominicis.pairEndpointInversionCount
        (d.componentPairEquiv orders shuffle ⟨B, p⟩).1
        (d.componentPairEquiv orders shuffle ⟨C, q⟩).1 % 2 = 1 ↔
      Common.BlochDeDominicis.Crosses
          (d.componentPairEquiv orders shuffle ⟨B, p⟩).1
          (d.componentPairEquiv orders shuffle ⟨C, q⟩).1 ∨
        Common.BlochDeDominicis.Crosses
          (d.componentPairEquiv orders shuffle ⟨C, q⟩).1
          (d.componentPairEquiv orders shuffle ⟨B, p⟩).1 := by
  let globalPairing := d.pairingInOrder (d.assembleVertexOrder orders shuffle)
  let globalP : globalPairing.NormalizedPair := d.componentPairEquiv orders shuffle ⟨B, p⟩
  let globalQ : globalPairing.NormalizedPair := d.componentPairEquiv orders shuffle ⟨C, q⟩
  have hne : globalP ≠ globalQ := by
    intro h
    have hsigma := (d.componentPairEquiv orders shuffle).injective h
    exact hBC (congrArg Sigma.fst hsigma)
  have hEnds := globalPairing.normalizedPair_endpoints_ne_of_ne globalP globalQ hne
  exact Common.BlochDeDominicis.pairEndpointInversionCount_mod_two_eq_one_iff_crosses
    globalP.1 globalQ.1
    (globalPairing.pairs_normalized globalP.2)
    (globalPairing.pairs_normalized globalQ.2)
    hEnds.1 hEnds.2.1 hEnds.2.2.1 hEnds.2.2.2

end SecondQuantization
