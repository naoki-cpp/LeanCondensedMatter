import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Pairing.ComponentPairProduct
import LeanCondensedMatter.Combinatorics.PerfectPairing.ComponentCrossing
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.PairingWeight

set_option linter.style.header false

/-!
# Component factorization of quartic crossing parity

The crossing count of an assembled global pairing is the double sum of oriented crossing counts over
connected components. Two pairs taken from distinct components have disjoint endpoints, so their
crossing parity is the parity of the four endpoint comparisons. Reindexing those comparisons by the
flattened legs of the two components makes each vertex contribute a whole four-leg block, hence a
multiple of four. The off-diagonal contributions therefore cancel modulo two, leaving the
component-local crossing counts and with them the factorization of the pairing weight over
connected components.

This layer is label-, statistics-realization-, and state-independent. The final weight theorem is
parameterized only by `Statistics`.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {Label : Type*} {N : ℕ}

/-- For distinct components, comparison of assembled legs is exactly comparison of their global
vertex slots. -/
private theorem QuarticDiagram.componentOrderedLeg_lt_iff_slot_lt
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S) (shuffle : d.ComponentShuffle)
    (B C : d.componentPartition.parts) (hBC : B ≠ C)
    (p : Fin (2 * (2 * (B : Finset (Fin N)).card)))
    (q : Fin (2 * (2 * (C : Finset (Fin N)).card))) :
    d.componentOrderedLeg shuffle B p < d.componentOrderedLeg shuffle C q ↔
      shuffle.slotEquiv
          ⟨B, (orderedQuarticLegEquiv (B : Finset (Fin N)).card p).1⟩ <
        shuffle.slotEquiv
          ⟨C, (orderedQuarticLegEquiv (C : Finset (Fin N)).card q).1⟩ := by
  have hslot_ne :
      shuffle.slotEquiv
          ⟨B, (orderedQuarticLegEquiv (B : Finset (Fin N)).card p).1⟩ ≠
        shuffle.slotEquiv
          ⟨C, (orderedQuarticLegEquiv (C : Finset (Fin N)).card q).1⟩ := by
    intro hslot
    have hsigma := shuffle.slotEquiv.injective hslot
    exact hBC (congrArg Sigma.fst hsigma)
  unfold QuarticDiagram.componentOrderedLeg
  exact orderedQuarticLegEquiv_symm_lt_symm_iff_fst_lt_of_ne S.card
    (shuffle.slotEquiv
      ⟨B, (orderedQuarticLegEquiv (B : Finset (Fin N)).card p).1⟩)
    (shuffle.slotEquiv
      ⟨C, (orderedQuarticLegEquiv (C : Finset (Fin N)).card q).1⟩)
    (orderedQuarticLegEquiv (B : Finset (Fin N)).card p).2
    (orderedQuarticLegEquiv (C : Finset (Fin N)).card q).2 hslot_ne

/-- Each leg of one component is preceded by whole four-leg vertex blocks of any other component, so
the total number of leg-order inversions between two distinct components is even. -/
private theorem QuarticDiagram.sum_componentOrderedLeg_inversions_mod_two_eq_zero
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S) (shuffle : d.ComponentShuffle)
    (B C : d.componentPartition.parts) (hBC : B ≠ C) :
    (∑ p : Fin (2 * (2 * (B : Finset (Fin N)).card)),
      ∑ q : Fin (2 * (2 * (C : Finset (Fin N)).card)),
        if d.componentOrderedLeg shuffle C q < d.componentOrderedLeg shuffle B p
        then 1 else 0) % 2 = 0 := by
  classical
  apply Nat.mod_eq_zero_of_dvd
  rw [Finset.sum_comm]
  refine Finset.dvd_sum fun q _ => ?_
  simp_rw [d.componentOrderedLeg_lt_iff_slot_lt shuffle C B (Ne.symm hBC)]
  rw [← Equiv.sum_comp (orderedQuarticLegEquiv (B : Finset (Fin N)).card).symm,
    Fintype.sum_prod_type]
  simp only [Equiv.apply_symm_apply]
  refine Finset.dvd_sum fun i _ => ?_
  rw [Fin.sum_univ_four]
  split_ifs <;> omega

/-- Both orientations of the crossing count between two distinct components add up to an even
number. -/
private theorem QuarticDiagram.componentCrossingCount_add_swap_mod_two_eq_zero
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B C : d.componentPartition.parts) (hBC : B ≠ C) :
    ((d.pairingInOrder (d.assembleVertexOrder orders shuffle)).componentCrossingCount
        (d.componentPairEquiv orders shuffle) B C +
      (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).componentCrossingCount
        (d.componentPairEquiv orders shuffle) C B) % 2 = 0 := by
  classical
  have hor := Combinatorics.Pairing.componentGeometricCrossingCount_eq_oriented_add
    (d.pairingInOrder (d.assembleVertexOrder orders shuffle))
    (d.componentPairEquiv orders shuffle) B C
  rw [← hor]
  have hcross :=
    Combinatorics.Pairing.componentGeometricCrossingCount_mod_two_eq_endpointInversionCount
      (d.pairingInOrder (d.assembleVertexOrder orders shuffle))
      (d.componentPairEquiv orders shuffle)
      (fun B => ((d.restrictComponent B.2).pairingInOrder (orders B)).pairEndpointEquiv)
      (fun B p => d.componentOrderedLeg shuffle B p)
      (fun B p k => by
        fin_cases k <;>
        simp [Combinatorics.Pairing.pairEndpointEquiv_apply,
          Combinatorics.Pairing.pairEndpoint, Combinatorics.pairEndpointAt,
          d.componentPairEquiv_apply])
      B C hBC
  rw [hcross]
  exact d.sum_componentOrderedLeg_inversions_mod_two_eq_zero shuffle B C hBC

/-- The diagonal oriented crossing count is the local crossing count of that component. -/
private theorem QuarticDiagram.componentCrossingCount_self
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts) :
    (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).componentCrossingCount
        (d.componentPairEquiv orders shuffle) B B =
      ((d.restrictComponent B.2).pairingInOrder (orders B)).crossingCount := by
  classical
  rw [Combinatorics.Pairing.componentCrossingCount, Fintype.sum_prod_type,
    Combinatorics.Pairing.crossingCount_eq_sum_sum_crosses]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [d.componentPairEquiv_apply, d.componentPairEquiv_apply]
  rw [Combinatorics.crosses_map_iff
    (d.componentOrderedLeg shuffle B)
    (d.componentOrderedLeg_strictMono shuffle B)
    p.1.1 p.1.2 q.1.1 q.1.2]

/-- The assembled global crossing count has the same parity as the sum of component-local crossing
counts. -/
theorem QuarticDiagram.pairingInOrder_crossingCount_mod_two_eq_sum_components
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle) :
    (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).crossingCount % 2 =
      (∑ B : d.componentPartition.parts,
        ((d.restrictComponent B.2).pairingInOrder (orders B)).crossingCount) % 2 := by
  rw [Combinatorics.Pairing.crossingCount_mod_two_eq_sum_componentCrossingCount
    (d.pairingInOrder (d.assembleVertexOrder orders shuffle))
    (d.componentPairEquiv orders shuffle)
    (fun B C hBC =>
      d.componentCrossingCount_add_swap_mod_two_eq_zero orders shuffle B C hBC)]
  apply congrArg (fun n : ℕ => n % 2)
  apply Finset.sum_congr rfl
  intro B _
  exact d.componentCrossingCount_self orders shuffle B

/-- Pairing weight factors over connected components for every component shuffle. -/
theorem QuarticDiagram.pairingInOrder_weight_eq_prod_components
    (s : Statistics) {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle) :
    (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).weight s =
      ∏ B : d.componentPartition.parts,
        ((d.restrictComponent B.2).pairingInOrder (orders B)).weight s := by
  exact BlochDeDominicis.Pairing.weight_eq_prod_of_crossingCount_mod_two_eq
    s
    (d.pairingInOrder (d.assembleVertexOrder orders shuffle))
    (fun B : d.componentPartition.parts =>
      (d.restrictComponent B.2).pairingInOrder (orders B))
    (d.pairingInOrder_crossingCount_mod_two_eq_sum_components orders shuffle)

end Common
end SecondQuantization
