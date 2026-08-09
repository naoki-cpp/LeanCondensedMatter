import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentPairProduct
import LeanCondensedMatter.Combinatorics.PerfectPairing.CrossingParity
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
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} {N : ℕ}

/-- For distinct components, comparison of assembled legs is exactly comparison of their global
vertex slots. -/
private theorem QuarticWickDiagram.componentOrderedLeg_lt_iff_slot_lt
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) (shuffle : d.ComponentShuffle)
    (B C : d.componentPartition.parts) (hBC : B ≠ C)
    (p : Fin (2 * (2 * (B : Finset (Fin N)).card)))
    (q : Fin (2 * (2 * (C : Finset (Fin N)).card))) :
    d.componentOrderedLeg shuffle B p < d.componentOrderedLeg shuffle C q ↔
      shuffle.slotEquiv
          ⟨B, (Common.orderedQuarticLegEquiv (B : Finset (Fin N)).card p).1⟩ <
        shuffle.slotEquiv
          ⟨C, (Common.orderedQuarticLegEquiv (C : Finset (Fin N)).card q).1⟩ := by
  have hslot_ne :
      shuffle.slotEquiv
          ⟨B, (Common.orderedQuarticLegEquiv (B : Finset (Fin N)).card p).1⟩ ≠
        shuffle.slotEquiv
          ⟨C, (Common.orderedQuarticLegEquiv (C : Finset (Fin N)).card q).1⟩ := by
    intro hslot
    have hsigma := shuffle.slotEquiv.injective hslot
    exact hBC (congrArg Sigma.fst hsigma)
  unfold Common.QuarticDiagram.componentOrderedLeg
  exact orderedQuarticLegEquiv_symm_lt_symm_iff_fst_lt_of_ne S.card
    (shuffle.slotEquiv
      ⟨B, (Common.orderedQuarticLegEquiv (B : Finset (Fin N)).card p).1⟩)
    (shuffle.slotEquiv
      ⟨C, (Common.orderedQuarticLegEquiv (C : Finset (Fin N)).card q).1⟩)
    (Common.orderedQuarticLegEquiv (B : Finset (Fin N)).card p).2
    (Common.orderedQuarticLegEquiv (C : Finset (Fin N)).card q).2 hslot_ne

/-- Each leg of one component is preceded by whole four-leg vertex blocks of any other component, so
the total number of leg-order inversions between two distinct components is even. -/
private theorem QuarticWickDiagram.sum_componentOrderedLeg_inversions_mod_two_eq_zero
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) (shuffle : d.ComponentShuffle)
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
  rw [← Equiv.sum_comp (Common.orderedQuarticLegEquiv (B : Finset (Fin N)).card).symm,
    Fintype.sum_prod_type]
  simp only [Equiv.apply_symm_apply]
  refine Finset.dvd_sum fun i _ => ?_
  rw [Fin.sum_univ_four]
  split_ifs <;> omega

/-- Selecting an endpoint after transporting a component-local pair is the same as transporting the
selected local endpoint. -/
private theorem QuarticWickDiagram.pairEndpointAt_componentPairEquiv
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts) (p : d.LocalOrderedPair orders B) (k : Fin 2) :
    Combinatorics.pairEndpointAt
        (d.componentPairEquiv orders shuffle ⟨B, p⟩).1 k =
      d.componentOrderedLeg shuffle B
        (Combinatorics.pairEndpointAt p.1 k) := by
  fin_cases k <;>
  simp [Combinatorics.pairEndpointAt, d.componentPairEquiv_apply]

/-- Endpoint inversion count written using component-local endpoints and their global embeddings. -/
private theorem QuarticWickDiagram.componentPairEndpointInversionCount_eq_sum
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B C : d.componentPartition.parts)
    (p : d.LocalOrderedPair orders B) (q : d.LocalOrderedPair orders C) :
    Combinatorics.pairEndpointInversionCount
        (d.componentPairEquiv orders shuffle ⟨B, p⟩).1
        (d.componentPairEquiv orders shuffle ⟨C, q⟩).1 =
      ∑ i : Fin 2, ∑ j : Fin 2,
        if d.componentOrderedLeg shuffle C
            (Combinatorics.pairEndpointAt q.1 j) <
          d.componentOrderedLeg shuffle B
            (Combinatorics.pairEndpointAt p.1 i)
        then 1 else 0 := by
  rw [Combinatorics.pairEndpointInversionCount_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [d.pairEndpointAt_componentPairEquiv, d.pairEndpointAt_componentPairEquiv]

/-- Reindex the pair-endpoint inversion sum as a sum over all legs of the two components. -/
private theorem
    QuarticWickDiagram.sum_componentPairEndpointInversionCount_eq_sum_componentOrderedLeg_inversions
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B C : d.componentPartition.parts) :
    (∑ x : d.LocalOrderedPair orders B × d.LocalOrderedPair orders C,
      Combinatorics.pairEndpointInversionCount
        (d.componentPairEquiv orders shuffle ⟨B, x.1⟩).1
        (d.componentPairEquiv orders shuffle ⟨C, x.2⟩).1) =
      ∑ p : Fin (2 * (2 * (B : Finset (Fin N)).card)),
        ∑ q : Fin (2 * (2 * (C : Finset (Fin N)).card)),
          if d.componentOrderedLeg shuffle C q < d.componentOrderedLeg shuffle B p
          then 1 else 0 := by
  classical
  let localPairingB := (d.restrictComponent B.2).pairingInOrder (orders B)
  let localPairingC := (d.restrictComponent C.2).pairingInOrder (orders C)
  let endpointPairEquiv :
      ((d.LocalOrderedPair orders B × d.LocalOrderedPair orders C) × (Fin 2 × Fin 2)) ≃
        (Fin (2 * (2 * (B : Finset (Fin N)).card)) ×
          Fin (2 * (2 * (C : Finset (Fin N)).card))) :=
    (Equiv.prodProdProdComm _ _ _ _).trans
      (Equiv.prodCongr localPairingB.pairEndpointEquiv localPairingC.pairEndpointEquiv)
  calc
    (∑ x : d.LocalOrderedPair orders B × d.LocalOrderedPair orders C,
        Combinatorics.pairEndpointInversionCount
          (d.componentPairEquiv orders shuffle ⟨B, x.1⟩).1
          (d.componentPairEquiv orders shuffle ⟨C, x.2⟩).1) =
      ∑ x : (d.LocalOrderedPair orders B × d.LocalOrderedPair orders C) × (Fin 2 × Fin 2),
        if d.componentOrderedLeg shuffle C
            (Combinatorics.pairEndpointAt x.1.2.1 x.2.2) <
          d.componentOrderedLeg shuffle B
            (Combinatorics.pairEndpointAt x.1.1.1 x.2.1)
        then 1 else 0 := by
          simp only [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro p _
          apply Finset.sum_congr rfl
          intro q _
          exact d.componentPairEndpointInversionCount_eq_sum orders shuffle B C p q
    _ = ∑ x : Fin (2 * (2 * (B : Finset (Fin N)).card)) ×
          Fin (2 * (2 * (C : Finset (Fin N)).card)),
        if d.componentOrderedLeg shuffle C x.2 < d.componentOrderedLeg shuffle B x.1
        then 1 else 0 := by
          refine Fintype.sum_equiv endpointPairEquiv
            (fun x => if d.componentOrderedLeg shuffle C
                (Combinatorics.pairEndpointAt x.1.2.1 x.2.2) <
              d.componentOrderedLeg shuffle B
                (Combinatorics.pairEndpointAt x.1.1.1 x.2.1)
              then 1 else 0)
            (fun x => if d.componentOrderedLeg shuffle C x.2 <
              d.componentOrderedLeg shuffle B x.1 then 1 else 0) ?_
          intro x
          rfl
    _ = ∑ p : Fin (2 * (2 * (B : Finset (Fin N)).card)),
        ∑ q : Fin (2 * (2 * (C : Finset (Fin N)).card)),
          if d.componentOrderedLeg shuffle C q < d.componentOrderedLeg shuffle B p
          then 1 else 0 := by
          rw [Fintype.sum_prod_type]

/-- Indicator-valued version of component-pair crossing parity. -/
private theorem QuarticWickDiagram.componentPairEndpointInversionCount_mod_two_eq_crossesIndicator
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B C : d.componentPartition.parts) (hBC : B ≠ C)
    (p : d.LocalOrderedPair orders B) (q : d.LocalOrderedPair orders C) :
    Combinatorics.pairEndpointInversionCount
        (d.componentPairEquiv orders shuffle ⟨B, p⟩).1
        (d.componentPairEquiv orders shuffle ⟨C, q⟩).1 % 2 =
      if Combinatorics.Crosses
          (d.componentPairEquiv orders shuffle ⟨B, p⟩).1
          (d.componentPairEquiv orders shuffle ⟨C, q⟩).1 ∨
        Combinatorics.Crosses
          (d.componentPairEquiv orders shuffle ⟨C, q⟩).1
          (d.componentPairEquiv orders shuffle ⟨B, p⟩).1
      then 1 else 0 := by
  have hPairNe :
      d.componentPairEquiv orders shuffle ⟨B, p⟩ ≠
        d.componentPairEquiv orders shuffle ⟨C, q⟩ := by
    intro h
    exact hBC (congrArg Sigma.fst ((d.componentPairEquiv orders shuffle).injective h))
  have hEnds :=
    (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).normalizedPair_endpoints_ne_of_ne
      (d.componentPairEquiv orders shuffle ⟨B, p⟩)
      (d.componentPairEquiv orders shuffle ⟨C, q⟩) hPairNe
  exact Combinatorics.pairEndpointInversionCount_mod_two_eq_crossesIndicator
    (d.componentPairEquiv orders shuffle ⟨B, p⟩).1
    (d.componentPairEquiv orders shuffle ⟨C, q⟩).1
    ((d.pairingInOrder (d.assembleVertexOrder orders shuffle)).pairs_normalized
      (d.componentPairEquiv orders shuffle ⟨B, p⟩).2)
    ((d.pairingInOrder (d.assembleVertexOrder orders shuffle)).pairs_normalized
      (d.componentPairEquiv orders shuffle ⟨C, q⟩).2)
    hEnds.1 hEnds.2.1 hEnds.2.2.1 hEnds.2.2.2

/-- Oriented crossing count from pairs in component `B` to pairs in component `C`. -/
private noncomputable def QuarticWickDiagram.componentOrientedCrossingCount
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B C : d.componentPartition.parts) : ℕ :=
  ∑ x : d.LocalOrderedPair orders B × d.LocalOrderedPair orders C,
    if Combinatorics.Crosses
        (d.componentPairEquiv orders shuffle ⟨B, x.1⟩).1
        (d.componentPairEquiv orders shuffle ⟨C, x.2⟩).1
    then 1 else 0

/-- Both orientations of the crossing count between two distinct components add up to an even
number. -/
private theorem QuarticWickDiagram.componentOrientedCrossingCount_add_swap_mod_two_eq_zero
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B C : d.componentPartition.parts) (hBC : B ≠ C) :
    (d.componentOrientedCrossingCount orders shuffle B C +
      d.componentOrientedCrossingCount orders shuffle C B) % 2 = 0 := by
  classical
  have hswap : d.componentOrientedCrossingCount orders shuffle C B =
      ∑ x : d.LocalOrderedPair orders B × d.LocalOrderedPair orders C,
        if Combinatorics.Crosses
            (d.componentPairEquiv orders shuffle ⟨C, x.2⟩).1
            (d.componentPairEquiv orders shuffle ⟨B, x.1⟩).1
        then 1 else 0 := by
    rw [QuarticWickDiagram.componentOrientedCrossingCount,
      ← Equiv.sum_comp (Equiv.prodComm
        (d.LocalOrderedPair orders B) (d.LocalOrderedPair orders C))]
    rfl
  have hor : d.componentOrientedCrossingCount orders shuffle B C +
      d.componentOrientedCrossingCount orders shuffle C B =
      ∑ x : d.LocalOrderedPair orders B × d.LocalOrderedPair orders C,
        if Combinatorics.Crosses
            (d.componentPairEquiv orders shuffle ⟨B, x.1⟩).1
            (d.componentPairEquiv orders shuffle ⟨C, x.2⟩).1 ∨
          Combinatorics.Crosses
            (d.componentPairEquiv orders shuffle ⟨C, x.2⟩).1
            (d.componentPairEquiv orders shuffle ⟨B, x.1⟩).1
        then 1 else 0 := by
    rw [hswap, QuarticWickDiagram.componentOrientedCrossingCount, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hbc : Combinatorics.Crosses
        (d.componentPairEquiv orders shuffle ⟨B, x.1⟩).1
        (d.componentPairEquiv orders shuffle ⟨C, x.2⟩).1
    · have hcb : ¬ Combinatorics.Crosses
          (d.componentPairEquiv orders shuffle ⟨C, x.2⟩).1
          (d.componentPairEquiv orders shuffle ⟨B, x.1⟩).1 :=
        fun h => lt_asymm hbc.1 h.1
      simp [hbc, hcb]
    · simp [hbc]
  have hinv :
      (∑ x : d.LocalOrderedPair orders B × d.LocalOrderedPair orders C,
        if Combinatorics.Crosses
            (d.componentPairEquiv orders shuffle ⟨B, x.1⟩).1
            (d.componentPairEquiv orders shuffle ⟨C, x.2⟩).1 ∨
          Combinatorics.Crosses
            (d.componentPairEquiv orders shuffle ⟨C, x.2⟩).1
            (d.componentPairEquiv orders shuffle ⟨B, x.1⟩).1
        then 1 else 0) % 2 =
      (∑ x : d.LocalOrderedPair orders B × d.LocalOrderedPair orders C,
        Combinatorics.pairEndpointInversionCount
          (d.componentPairEquiv orders shuffle ⟨B, x.1⟩).1
          (d.componentPairEquiv orders shuffle ⟨C, x.2⟩).1) % 2 := by
    symm
    exact Combinatorics.fintype_sum_mod_two_congr _ _ fun x => by
      have h := d.componentPairEndpointInversionCount_mod_two_eq_crossesIndicator
        orders shuffle B C hBC x.1 x.2
      split_ifs at h ⊢ <;> simpa using h
  rw [hor, hinv,
    d.sum_componentPairEndpointInversionCount_eq_sum_componentOrderedLeg_inversions
      orders shuffle B C]
  exact d.sum_componentOrderedLeg_inversions_mod_two_eq_zero shuffle B C hBC

private theorem QuarticWickDiagram.crosses_componentPairEquiv_iff
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts) (p q : d.LocalOrderedPair orders B) :
    Combinatorics.Crosses
        (d.componentPairEquiv orders shuffle ⟨B, p⟩).1
        (d.componentPairEquiv orders shuffle ⟨B, q⟩).1 ↔
      Combinatorics.Crosses p.1 q.1 := by
  rw [d.componentPairEquiv_apply, d.componentPairEquiv_apply]
  exact Combinatorics.crosses_map_iff
    (d.componentOrderedLegOrderEmbedding shuffle B)
    (d.componentOrderedLegOrderEmbedding shuffle B).strictMono
    p.1.1 p.1.2 q.1.1 q.1.2

/-- The diagonal oriented crossing count is the local crossing count of that component. -/
private theorem QuarticWickDiagram.componentOrientedCrossingCount_self
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts) :
    d.componentOrientedCrossingCount orders shuffle B B =
      ((d.restrictComponent B.2).pairingInOrder (orders B)).crossingCount := by
  classical
  rw [QuarticWickDiagram.componentOrientedCrossingCount, Fintype.sum_prod_type,
    Combinatorics.Pairing.crossingCount_eq_sum_sum_crosses]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  simp only [d.crosses_componentPairEquiv_iff]

/-- The assembled global crossing count is the double sum of oriented crossing counts over
components. -/
private theorem
    QuarticWickDiagram.pairingInOrder_crossingCount_eq_sum_componentOrientedCrossingCount
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle) :
    (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).crossingCount =
      ∑ B : d.componentPartition.parts,
        ∑ C : d.componentPartition.parts,
          d.componentOrientedCrossingCount orders shuffle B C := by
  classical
  let globalPairing := d.pairingInOrder (d.assembleVertexOrder orders shuffle)
  let pairEquiv := d.componentPairEquiv orders shuffle
  let componentPairProductEquiv :
      (Σ BC : d.componentPartition.parts × d.componentPartition.parts,
        d.LocalOrderedPair orders BC.1 × d.LocalOrderedPair orders BC.2) ≃
        d.GlobalOrderedPair orders shuffle × d.GlobalOrderedPair orders shuffle :=
    let sigmaProductEquiv :
        (Σ BC : d.componentPartition.parts × d.componentPartition.parts,
          d.LocalOrderedPair orders BC.1 × d.LocalOrderedPair orders BC.2) ≃
          (Σ B : d.componentPartition.parts, d.LocalOrderedPair orders B) ×
            (Σ C : d.componentPartition.parts, d.LocalOrderedPair orders C) := {
      toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
      invFun x := ⟨(x.1.1, x.2.1), (x.1.2, x.2.2)⟩
      left_inv := by rintro ⟨⟨B, C⟩, p, q⟩; rfl
      right_inv := by rintro ⟨⟨B, p⟩, ⟨C, q⟩⟩; rfl }
    sigmaProductEquiv.trans (Equiv.prodCongr pairEquiv pairEquiv)
  rw [globalPairing.crossingCount_eq_sum_crosses,
    ← Equiv.sum_comp componentPairProductEquiv,
    Fintype.sum_sigma, Fintype.sum_prod_type]
  rfl

/-- The assembled global crossing count has the same parity as the sum of component-local crossing
counts. -/
theorem QuarticWickDiagram.pairingInOrder_crossingCount_mod_two_eq_sum_components
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle) :
    (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).crossingCount % 2 =
      (∑ B : d.componentPartition.parts,
        ((d.restrictComponent B.2).pairingInOrder (orders B)).crossingCount) % 2 := by
  rw [d.pairingInOrder_crossingCount_eq_sum_componentOrientedCrossingCount
    orders shuffle]
  calc
    (∑ B : d.componentPartition.parts,
        ∑ C : d.componentPartition.parts,
          d.componentOrientedCrossingCount orders shuffle B C) % 2 =
      (∑ B : d.componentPartition.parts,
        d.componentOrientedCrossingCount orders shuffle B B) % 2 := by
          exact Combinatorics.fintype_sum_sum_modEq_diag_of_pair_add_modEq_zero
            2 (fun B C => d.componentOrientedCrossingCount orders shuffle B C)
            (fun B C hBC => by
              show (d.componentOrientedCrossingCount orders shuffle B C +
                d.componentOrientedCrossingCount orders shuffle C B) % 2 = 0 % 2
              simpa using d.componentOrientedCrossingCount_add_swap_mod_two_eq_zero
                orders shuffle B C hBC)
    _ = (∑ B : d.componentPartition.parts,
        ((d.restrictComponent B.2).pairingInOrder (orders B)).crossingCount) % 2 := by
          apply congrArg (fun n : ℕ => n % 2)
          apply Finset.sum_congr rfl
          intro B _
          exact d.componentOrientedCrossingCount_self orders shuffle B

/-- Pairing weight factors over connected components for every component shuffle. -/
theorem QuarticWickDiagram.pairingInOrder_weight_eq_prod_components
    (s : Common.Statistics) {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle) :
    (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).weight s =
      ∏ B : d.componentPartition.parts,
        ((d.restrictComponent B.2).pairingInOrder (orders B)).weight s := by
  exact Common.BlochDeDominicis.Pairing.weight_eq_prod_of_crossingCount_mod_two_eq
    s
    (d.pairingInOrder (d.assembleVertexOrder orders shuffle))
    (fun B : d.componentPartition.parts =>
      (d.restrictComponent B.2).pairingInOrder (orders B))
    (d.pairingInOrder_crossingCount_mod_two_eq_sum_components orders shuffle)

end Fermionic
end SecondQuantization
