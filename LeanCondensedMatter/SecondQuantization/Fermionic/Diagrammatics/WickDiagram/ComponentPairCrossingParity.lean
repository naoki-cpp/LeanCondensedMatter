import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentCrossing
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentLegInversion
import LeanCondensedMatter.Combinatorics.PerfectPairing.PairEndpoints
import LeanCondensedMatter.Combinatorics.PerfectPairing.CrossingParity

set_option linter.style.header false

/-!
# Endpoint inversion parity for pairs in distinct components

Pairs transported from different connected components are distinct normalized pairs of the assembled
global pairing. Their endpoints are therefore disjoint, so the generic endpoint-inversion parity
criterion applies directly. Reindexing normalized-pair endpoints by `Pairing.pairEndpointEquiv`
then reduces the total parity for two components to quartic vertex-block inversions, each of size
`4 × 4 = 16`.
-/

namespace SecondQuantization

variable {Mode : Type*} {N : ℕ}

@[simp]
theorem Common.BlochDeDominicis.Pairing.pairEndpoint_eq_pairEndpointAt {n : ℕ}
    (pairing : Common.BlochDeDominicis.Pairing n) (p : pairing.NormalizedPair) (k : Fin 2) :
    pairing.pairEndpoint (p, k) = Common.BlochDeDominicis.pairEndpointAt p.1 k :=
  rfl

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

/-- Indicator-valued version of component-pair crossing parity. -/
theorem QuarticWickDiagram.componentPairEndpointInversionCount_mod_two_eq_crossesIndicator
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B C : d.componentPartition.parts) (hBC : B ≠ C)
    (p : d.LocalOrderedPair orders B) (q : d.LocalOrderedPair orders C) :
    Common.BlochDeDominicis.pairEndpointInversionCount
        (d.componentPairEquiv orders shuffle ⟨B, p⟩).1
        (d.componentPairEquiv orders shuffle ⟨C, q⟩).1 % 2 =
      if Common.BlochDeDominicis.Crosses
          (d.componentPairEquiv orders shuffle ⟨B, p⟩).1
          (d.componentPairEquiv orders shuffle ⟨C, q⟩).1 ∨
        Common.BlochDeDominicis.Crosses
          (d.componentPairEquiv orders shuffle ⟨C, q⟩).1
          (d.componentPairEquiv orders shuffle ⟨B, p⟩).1
      then 1 else 0 := by
  let globalPairing := d.pairingInOrder (d.assembleVertexOrder orders shuffle)
  let globalP : globalPairing.NormalizedPair := d.componentPairEquiv orders shuffle ⟨B, p⟩
  let globalQ : globalPairing.NormalizedPair := d.componentPairEquiv orders shuffle ⟨C, q⟩
  have hne : globalP ≠ globalQ := by
    intro h
    have hsigma := (d.componentPairEquiv orders shuffle).injective h
    exact hBC (congrArg Sigma.fst hsigma)
  have hEnds := globalPairing.normalizedPair_endpoints_ne_of_ne globalP globalQ hne
  exact Common.BlochDeDominicis.pairEndpointInversionCount_mod_two_eq_crossesIndicator
    globalP.1 globalQ.1
    (globalPairing.pairs_normalized globalP.2)
    (globalPairing.pairs_normalized globalQ.2)
    hEnds.1 hEnds.2.1 hEnds.2.2.1 hEnds.2.2.2

/-- Selecting an endpoint after transporting a component-local pair is the same as transporting the
selected local endpoint. -/
@[simp]
theorem QuarticWickDiagram.pairEndpointAt_componentPairEquiv
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts) (p : d.LocalOrderedPair orders B) (k : Fin 2) :
    Common.BlochDeDominicis.pairEndpointAt
        (d.componentPairEquiv orders shuffle ⟨B, p⟩).1 k =
      d.componentOrderedLeg shuffle B
        (Common.BlochDeDominicis.pairEndpointAt p.1 k) := by
  fin_cases k <;>
  simp [Common.BlochDeDominicis.pairEndpointAt, d.componentPairEquiv_apply]

/-- Endpoint inversion count written using component-local endpoints and their global embeddings. -/
theorem QuarticWickDiagram.componentPairEndpointInversionCount_eq_sum
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B C : d.componentPartition.parts)
    (p : d.LocalOrderedPair orders B) (q : d.LocalOrderedPair orders C) :
    Common.BlochDeDominicis.pairEndpointInversionCount
        (d.componentPairEquiv orders shuffle ⟨B, p⟩).1
        (d.componentPairEquiv orders shuffle ⟨C, q⟩).1 =
      ∑ i : Fin 2, ∑ j : Fin 2,
        if d.componentOrderedLeg shuffle C
            (Common.BlochDeDominicis.pairEndpointAt q.1 j) <
          d.componentOrderedLeg shuffle B
            (Common.BlochDeDominicis.pairEndpointAt p.1 i)
        then 1 else 0 := by
  rw [Common.BlochDeDominicis.pairEndpointInversionCount_eq_sum]
  simp

/-- Number of geometric crossings between pairs belonging to two fixed distinct components. -/
noncomputable def QuarticWickDiagram.componentGeometricCrossingCount
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B C : d.componentPartition.parts) : ℕ :=
  ∑ x : d.LocalOrderedPair orders B × d.LocalOrderedPair orders C,
    if Common.BlochDeDominicis.Crosses
        (d.componentPairEquiv orders shuffle ⟨B, x.1⟩).1
        (d.componentPairEquiv orders shuffle ⟨C, x.2⟩).1 ∨
      Common.BlochDeDominicis.Crosses
        (d.componentPairEquiv orders shuffle ⟨C, x.2⟩).1
        (d.componentPairEquiv orders shuffle ⟨B, x.1⟩).1
    then 1 else 0

/-- Sum of the four-endpoint inversion counts between pairs in two fixed components. -/
noncomputable def QuarticWickDiagram.componentPairEndpointInversionSum
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B C : d.componentPartition.parts) : ℕ :=
  ∑ x : d.LocalOrderedPair orders B × d.LocalOrderedPair orders C,
    Common.BlochDeDominicis.pairEndpointInversionCount
      (d.componentPairEquiv orders shuffle ⟨B, x.1⟩).1
      (d.componentPairEquiv orders shuffle ⟨C, x.2⟩).1

/-- Geometric crossing count and endpoint-inversion sum agree modulo two. -/
theorem QuarticWickDiagram.componentGeometricCrossingCount_mod_two_eq_endpointInversionSum
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B C : d.componentPartition.parts) (hBC : B ≠ C) :
    d.componentGeometricCrossingCount orders shuffle B C % 2 =
      d.componentPairEndpointInversionSum orders shuffle B C % 2 := by
  symm
  exact Common.BlochDeDominicis.fintype_sum_mod_two_congr _ _ fun x =>
    d.componentPairEndpointInversionCount_mod_two_eq_crossesIndicator
      orders shuffle B C hBC x.1 x.2

/-- Reindex the pair-endpoint inversion sum as a sum over all local legs of the two components. -/
theorem QuarticWickDiagram.componentPairEndpointInversionSum_eq_sum_componentOrderedLeg_inversions
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B C : d.componentPartition.parts) :
    d.componentPairEndpointInversionSum orders shuffle B C =
      ∑ p : Fin (2 * (2 * (B : Finset (Fin N)).card)),
        ∑ q : Fin (2 * (2 * (C : Finset (Fin N)).card)),
          if d.componentOrderedLeg shuffle C q < d.componentOrderedLeg shuffle B p
          then 1 else 0 := by
  classical
  let localPairingB := (d.restrictComponent B.2).pairingInOrder (orders B)
  let localPairingC := (d.restrictComponent C.2).pairingInOrder (orders C)
  calc
    d.componentPairEndpointInversionSum orders shuffle B C =
      ∑ p : d.LocalOrderedPair orders B, ∑ q : d.LocalOrderedPair orders C,
        ∑ i : Fin 2, ∑ j : Fin 2,
          if d.componentOrderedLeg shuffle C
              (Common.BlochDeDominicis.pairEndpointAt q.1 j) <
            d.componentOrderedLeg shuffle B
              (Common.BlochDeDominicis.pairEndpointAt p.1 i)
          then 1 else 0 := by
            rw [QuarticWickDiagram.componentPairEndpointInversionSum,
              Fintype.sum_prod_type]
            apply Finset.sum_congr rfl
            intro p _
            apply Finset.sum_congr rfl
            intro q _
            exact d.componentPairEndpointInversionCount_eq_sum orders shuffle B C p q
    _ = ∑ p : d.LocalOrderedPair orders B, ∑ i : Fin 2,
        ∑ q : d.LocalOrderedPair orders C, ∑ j : Fin 2,
          if d.componentOrderedLeg shuffle C
              (Common.BlochDeDominicis.pairEndpointAt q.1 j) <
            d.componentOrderedLeg shuffle B
              (Common.BlochDeDominicis.pairEndpointAt p.1 i)
          then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro p _
            rw [Finset.sum_comm]
    _ = ∑ x : d.LocalOrderedPair orders B × Fin 2,
        ∑ y : d.LocalOrderedPair orders C × Fin 2,
          if d.componentOrderedLeg shuffle C
              (Common.BlochDeDominicis.pairEndpointAt y.1.1 y.2) <
            d.componentOrderedLeg shuffle B
              (Common.BlochDeDominicis.pairEndpointAt x.1.1 x.2)
          then 1 else 0 := by
            rw [Fintype.sum_prod_type]
            apply Finset.sum_congr rfl
            intro p _
            apply Finset.sum_congr rfl
            intro i _
            rw [Fintype.sum_prod_type]
    _ = ∑ p : Fin (2 * (2 * (B : Finset (Fin N)).card)),
        ∑ q : Fin (2 * (2 * (C : Finset (Fin N)).card)),
          if d.componentOrderedLeg shuffle C q < d.componentOrderedLeg shuffle B p
          then 1 else 0 := by
            simp_rw [← Common.BlochDeDominicis.Pairing.pairEndpoint_eq_pairEndpointAt]
            rw [Equiv.sum_comp localPairingB.pairEndpointEquiv]
            apply Finset.sum_congr rfl
            intro p _
            rw [Equiv.sum_comp localPairingC.pairEndpointEquiv]

/-- The pair-endpoint inversion sum between two distinct components is even. -/
theorem QuarticWickDiagram.componentPairEndpointInversionSum_mod_two_eq_zero
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B C : d.componentPartition.parts) (hBC : B ≠ C) :
    d.componentPairEndpointInversionSum orders shuffle B C % 2 = 0 := by
  rw [d.componentPairEndpointInversionSum_eq_sum_componentOrderedLeg_inversions
    orders shuffle B C,
    d.sum_componentOrderedLeg_inversions_eq_sum_vertex_inversions shuffle B C hBC]
  apply Nat.mod_eq_zero_of_dvd
  apply Finset.dvd_sum
  intro i _
  apply Finset.dvd_sum
  intro j _
  split_ifs <;> omega

/-- The geometric crossing count between any two distinct components is even. -/
theorem QuarticWickDiagram.componentGeometricCrossingCount_mod_two_eq_zero
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B C : d.componentPartition.parts) (hBC : B ≠ C) :
    d.componentGeometricCrossingCount orders shuffle B C % 2 = 0 := by
  rw [d.componentGeometricCrossingCount_mod_two_eq_endpointInversionSum
    orders shuffle B C hBC,
    d.componentPairEndpointInversionSum_mod_two_eq_zero orders shuffle B C hBC]

end SecondQuantization
