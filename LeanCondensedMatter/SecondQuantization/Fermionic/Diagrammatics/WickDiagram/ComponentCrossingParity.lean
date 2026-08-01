import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentCrossing
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.PairingWeight

set_option linter.style.header false

/-!
# External crossing parity reduction

The assembled global crossing pairs split into the within-component crossings identified in
`ComponentCrossing.lean` and their complement.  This file records the resulting cardinality and
parity decompositions, then reduces component-wise pairing-weight factorization to the single
remaining statement that the complementary crossing set has even cardinality.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} {N : ℕ}

/-- The assembled crossings whose two normalized pairs do not both come from one component. -/
noncomputable def QuarticWickDiagram.externalCrossingPairs {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (orders : d.ComponentVertexOrders)
    (shuffle : d.ComponentShuffle) :
    Finset (d.GlobalCrossingPair orders shuffle) := by
  classical
  exact Finset.univ \ d.internalCrossingPairs orders shuffle

/-- External and internal crossings partition all assembled global crossings. -/
theorem QuarticWickDiagram.card_externalCrossingPairs_add_card_internalCrossingPairs
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle) :
    (d.externalCrossingPairs orders shuffle).card +
        (d.internalCrossingPairs orders shuffle).card =
      (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).crossingCount := by
  classical
  rw [Combinatorics.Pairing.crossingCount_eq_card_crossingPair]
  simpa [QuarticWickDiagram.externalCrossingPairs] using
    Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ (d.internalCrossingPairs orders shuffle))

/-- The global crossing count is the sum of all component-local crossing counts plus the external
crossing contribution. -/
theorem QuarticWickDiagram.crossingCount_eq_sum_add_card_externalCrossingPairs
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle) :
    (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).crossingCount =
      (∑ B : d.componentPartition.parts,
        ((d.restrictComponent B.2).pairingInOrder (orders B)).crossingCount) +
      (d.externalCrossingPairs orders shuffle).card := by
  have h := d.card_externalCrossingPairs_add_card_internalCrossingPairs orders shuffle
  rw [d.card_internalCrossingPairs_eq_sum_crossingCount orders shuffle] at h
  omega

/-- If the external crossing contribution is even, the global crossing count has the same parity as
 the sum of all component-local crossing counts. -/
theorem QuarticWickDiagram.crossingCount_mod_two_eq_sum_of_externalCrossingPairs_mod_two_eq_zero
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (hExternal : (d.externalCrossingPairs orders shuffle).card % 2 = 0) :
    (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).crossingCount % 2 =
      (∑ B : d.componentPartition.parts,
        ((d.restrictComponent B.2).pairingInOrder (orders B)).crossingCount) % 2 := by
  rw [d.crossingCount_eq_sum_add_card_externalCrossingPairs orders shuffle,
    Nat.add_mod, hExternal]
  omega

/-- Component-wise pairing-weight factorization follows once the external crossings are proved even. -/
theorem QuarticWickDiagram.pairingInOrder_weight_eq_prod_components_of_externalCrossingPairs_mod_two_eq_zero
    (s : Common.Statistics) {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (hExternal : (d.externalCrossingPairs orders shuffle).card % 2 = 0) :
    (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).weight s =
      ∏ B : d.componentPartition.parts,
        ((d.restrictComponent B.2).pairingInOrder (orders B)).weight s := by
  exact Common.BlochDeDominicis.Pairing.weight_eq_prod_of_crossingCount_mod_two_eq
    s
    (d.pairingInOrder (d.assembleVertexOrder orders shuffle))
    (fun B : d.componentPartition.parts =>
      (d.restrictComponent B.2).pairingInOrder (orders B))
    (d.crossingCount_mod_two_eq_sum_of_externalCrossingPairs_mod_two_eq_zero
      orders shuffle hExternal)

end Fermionic
end SecondQuantization
