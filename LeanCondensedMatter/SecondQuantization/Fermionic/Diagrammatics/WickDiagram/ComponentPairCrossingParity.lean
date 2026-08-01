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

open Combinatorics

variable {Mode : Type*} {N : ℕ}

@[simp]
theorem Combinatorics.Pairing.pairEndpoint_eq_pairEndpointAt {n : ℕ}
    (pairing : Combinatorics.Pairing n) (p : pairing.NormalizedPair) (k : Fin 2) :
    pairing.pairEndpoint (p, k) = Combinatorics.pairEndpointAt p.1 k :=
  rfl

/-- Pairs transported from distinct components are distinct normalized global pairs. -/
theorem QuarticWickDiagram.componentPairEquiv_ne
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B C : d.componentPartition.parts) (hBC : B ≠ C)
    (p : d.LocalOrderedPair orders B) (q : d.LocalOrderedPair orders C) :
    d.componentPairEquiv orders shuffle ⟨B, p⟩ ≠
      d.componentPairEquiv orders shuffle ⟨C, q⟩ := by
  intro h
  exact hBC (congrArg Sigma.fst ((d.componentPairEquiv orders shuffle).injective h))

/-- Pairs transported from distinct components have disjoint global endpoints. -/
theorem QuarticWickDiagram.componentPairEquiv_endpoints_ne
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B C : d.componentPartition.parts) (hBC : B ≠ C)
    (p : d.LocalOrderedPair orders B) (q : d.LocalOrderedPair orders C) :
    (d.componentPairEquiv orders shuffle ⟨B, p⟩).1.1 ≠
        (d.componentPairEquiv orders shuffle ⟨C, q⟩).1.1 ∧
      (d.componentPairEquiv orders shuffle ⟨B, p⟩).1.1 ≠
        (d.componentPairEquiv orders shuffle ⟨C, q⟩).1.2 ∧
      (d.componentPairEquiv orders shuffle ⟨B, p⟩).1.2 ≠
        (d.componentPairEquiv orders shuffle ⟨C, q⟩).1.1 ∧
      (d.componentPairEquiv orders shuffle ⟨B, p⟩).1.2 ≠
        (d.componentPairEquiv orders shuffle ⟨C, q⟩).1.2 := by
  exact (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).normalizedPair_endpoints_ne_of_ne
    (d.componentPairEquiv orders shuffle ⟨B, p⟩)
    (d.componentPairEquiv orders shuffle ⟨C, q⟩)
    (d.componentPairEquiv_ne orders shuffle B C hBC p q)

/-- A pair from component `B` and a pair from a distinct component `C` cross geometrically exactly
when their four cross-pair endpoint comparisons have odd parity. -/
theorem QuarticWickDiagram.componentPairEndpointInversionCount_mod_two_eq_one_iff_crosses
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B C : d.componentPartition.parts) (hBC : B ≠ C)
    (p : d.LocalOrderedPair orders B) (q : d.LocalOrderedPair orders C) :
    Combinatorics.pairEndpointInversionCount
        (d.componentPairEquiv orders shuffle ⟨B, p⟩).1
        (d.componentPairEquiv orders shuffle ⟨C, q⟩).1 % 2 = 1 ↔
      Combinatorics.Crosses
          (d.componentPairEquiv orders shuffle ⟨B, p⟩).1
          (d.componentPairEquiv orders shuffle ⟨C, q⟩).1 ∨
        Combinatorics.Crosses
          (d.componentPairEquiv orders shuffle ⟨C, q⟩).1
          (d.componentPairEquiv orders shuffle ⟨B, p⟩).1 := by
  have hEnds := d.componentPairEquiv_endpoints_ne orders shuffle B C hBC p q
  exact Combinatorics.pairEndpointInversionCount_mod_two_eq_one_iff_crosses
    (d.componentPairEquiv orders shuffle ⟨B, p⟩).1
    (d.componentPairEquiv orders shuffle ⟨C, q⟩).1
    ((d.pairingInOrder (d.assembleVertexOrder orders shuffle)).pairs_normalized
      (d.componentPairEquiv orders shuffle ⟨B, p⟩).2)
    ((d.pairingInOrder (d.assembleVertexOrder orders shuffle)).pairs_normalized
      (d.componentPairEquiv orders shuffle ⟨C, q⟩).2)
    hEnds.1 hEnds.2.1 hEnds.2.2.1 hEnds.2.2.2

/-- Indicator-valued version of component-pair crossing parity. -/
theorem QuarticWickDiagram.componentPairEndpointInversionCount_mod_two_eq_crossesIndicator
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
  have hEnds := d.componentPairEquiv_endpoints_ne orders shuffle B C hBC p q
  exact Combinatorics.pairEndpointInversionCount_mod_two_eq_crossesIndicator
    (d.componentPairEquiv orders shuffle ⟨B, p⟩).1
    (d.componentPairEquiv orders shuffle ⟨C, q⟩).1
    ((d.pairingInOrder (d.assembleVertexOrder orders shuffle)).pairs_normalized
      (d.componentPairEquiv orders shuffle ⟨B, p⟩).2)
    ((d.pairingInOrder (d.assembleVertexOrder orders shuffle)).pairs_normalized
      (d.componentPairEquiv orders shuffle ⟨C, q⟩).2)
    hEnds.1 hEnds.2.1 hEnds.2.2.1 hEnds.2.2.2

/-- Selecting an endpoint after transporting a component-local pair is the same as transporting the
selected local endpoint. -/
@[simp]
theorem QuarticWickDiagram.pairEndpointAt_componentPairEquiv
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
theorem QuarticWickDiagram.componentPairEndpointInversionCount_eq_sum
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

/-- Number of geometric crossings between pairs belonging to two fixed distinct components. -/
noncomputable def QuarticWickDiagram.componentGeometricCrossingCount
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B C : d.componentPartition.parts) : ℕ :=
  ∑ x : d.LocalOrderedPair orders B × d.LocalOrderedPair orders C,
    if Combinatorics.Crosses
        (d.componentPairEquiv orders shuffle ⟨B, x.1⟩).1
        (d.componentPairEquiv orders shuffle ⟨C, x.2⟩).1 ∨
      Combinatorics.Crosses
        (d.componentPairEquiv orders shuffle ⟨C, x.2⟩).1
        (d.componentPairEquiv orders shuffle ⟨B, x.1⟩).1
    then 1 else 0

/-- Sum of the four-endpoint inversion counts between pairs in two fixed components. -/
noncomputable def QuarticWickDiagram.componentPairEndpointInversionSum
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B C : d.componentPartition.parts) : ℕ :=
  ∑ x : d.LocalOrderedPair orders B × d.LocalOrderedPair orders C,
    Combinatorics.pairEndpointInversionCount
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
  exact Combinatorics.fintype_sum_mod_two_congr _ _ fun x => by
    have h :=
      d.componentPairEndpointInversionCount_mod_two_eq_crossesIndicator
        orders shuffle B C hBC x.1 x.2
    split_ifs at h ⊢ <;> simpa using h

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
  let endpointPairEquiv :
      ((d.LocalOrderedPair orders B × d.LocalOrderedPair orders C) × (Fin 2 × Fin 2)) ≃
        (Fin (2 * (2 * (B : Finset (Fin N)).card)) ×
          Fin (2 * (2 * (C : Finset (Fin N)).card))) :=
    (Equiv.prodProdProdComm _ _ _ _).trans
      (Equiv.prodCongr localPairingB.pairEndpointEquiv localPairingC.pairEndpointEquiv)
  calc
    d.componentPairEndpointInversionSum orders shuffle B C =
      ∑ x : (d.LocalOrderedPair orders B × d.LocalOrderedPair orders C) × (Fin 2 × Fin 2),
        if d.componentOrderedLeg shuffle C
            (Combinatorics.pairEndpointAt x.1.2.1 x.2.2) <
          d.componentOrderedLeg shuffle B
            (Combinatorics.pairEndpointAt x.1.1.1 x.2.1)
        then 1 else 0 := by
          simp only [QuarticWickDiagram.componentPairEndpointInversionSum,
            Fintype.sum_prod_type]
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
