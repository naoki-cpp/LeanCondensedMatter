import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentPairCrossingParity
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentCrossingParity

set_option linter.style.header false

/-!
# Global component crossing parity

The global crossing count is reindexed as a double sum over connected components. Diagonal terms are
the component-local crossing counts. For distinct components, the two orientations combine into the
geometric crossing count proved even in `ComponentPairCrossingParity.lean`. Hence the global crossing
count agrees modulo two with the sum of its component-local crossing counts, the complementary
external crossing set is even, and the fermionic pairing weight factors over connected components.
-/

namespace SecondQuantization

open Combinatorics

variable {Mode : Type*} {N : ℕ}

private theorem crosses_asymm {n : ℕ}
    (p q : Fin (2 * n) × Fin (2 * n))
    (hpq : Combinatorics.Crosses p q) :
    ¬ Combinatorics.Crosses q p := by
  intro hqp
  exact lt_asymm hpq.1 hqp.1

private theorem indicator_or_eq_add_indicator_of_not_and
    (p q : Prop) [Decidable p] [Decidable q] (h : ¬ (p ∧ q)) :
    (if p ∨ q then 1 else 0 : ℕ) =
      (if p then 1 else 0) + (if q then 1 else 0) := by
  by_cases hp : p <;> by_cases hq : q <;> simp_all

/-- Oriented crossing count from pairs in component `B` to pairs in component `C`. -/
noncomputable def QuarticWickDiagram.componentOrientedCrossingCount
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B C : d.componentPartition.parts) : ℕ :=
  ∑ x : d.LocalOrderedPair orders B × d.LocalOrderedPair orders C,
    if Combinatorics.Crosses
        (d.componentPairEquiv orders shuffle ⟨B, x.1⟩).1
        (d.componentPairEquiv orders shuffle ⟨C, x.2⟩).1
    then 1 else 0

/-- The unoriented geometric crossing count is the sum of its two orientations. -/
theorem QuarticWickDiagram.componentGeometricCrossingCount_eq_oriented_add
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B C : d.componentPartition.parts) :
    d.componentGeometricCrossingCount orders shuffle B C =
      d.componentOrientedCrossingCount orders shuffle B C +
        d.componentOrientedCrossingCount orders shuffle C B := by
  classical
  let crossBC := fun x :
      d.LocalOrderedPair orders B × d.LocalOrderedPair orders C =>
    Combinatorics.Crosses
      (d.componentPairEquiv orders shuffle ⟨B, x.1⟩).1
      (d.componentPairEquiv orders shuffle ⟨C, x.2⟩).1
  let crossCB := fun x :
      d.LocalOrderedPair orders B × d.LocalOrderedPair orders C =>
    Combinatorics.Crosses
      (d.componentPairEquiv orders shuffle ⟨C, x.2⟩).1
      (d.componentPairEquiv orders shuffle ⟨B, x.1⟩).1
  have hswap :
      (∑ x : d.LocalOrderedPair orders C × d.LocalOrderedPair orders B,
        if Combinatorics.Crosses
            (d.componentPairEquiv orders shuffle ⟨C, x.1⟩).1
            (d.componentPairEquiv orders shuffle ⟨B, x.2⟩).1
        then 1 else 0) =
        ∑ x : d.LocalOrderedPair orders B × d.LocalOrderedPair orders C,
          if crossCB x then 1 else 0 := by
    rw [← Equiv.sum_comp (Equiv.prodComm
      (d.LocalOrderedPair orders B) (d.LocalOrderedPair orders C))]
    rfl
  rw [QuarticWickDiagram.componentGeometricCrossingCount,
    QuarticWickDiagram.componentOrientedCrossingCount,
    QuarticWickDiagram.componentOrientedCrossingCount, hswap]
  change (∑ x, if crossBC x ∨ crossCB x then 1 else 0) =
    (∑ x, if crossBC x then 1 else 0) + ∑ x, if crossCB x then 1 else 0
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  exact indicator_or_eq_add_indicator_of_not_and (crossBC x) (crossCB x) (by
    rintro ⟨hbc, hcb⟩
    exact crosses_asymm _ _ hbc hcb)

/-- The diagonal oriented crossing count is the local crossing count of that component. -/
theorem QuarticWickDiagram.componentOrientedCrossingCount_self
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
theorem QuarticWickDiagram.pairingInOrder_crossingCount_eq_sum_componentOrientedCrossingCount
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
              rw [← d.componentGeometricCrossingCount_eq_oriented_add
                orders shuffle B C]
              change d.componentGeometricCrossingCount orders shuffle B C % 2 = 0 % 2
              simpa using d.componentGeometricCrossingCount_mod_two_eq_zero
                orders shuffle B C hBC)
    _ = (∑ B : d.componentPartition.parts,
        ((d.restrictComponent B.2).pairingInOrder (orders B)).crossingCount) % 2 := by
          apply congrArg (fun n : ℕ => n % 2)
          apply Finset.sum_congr rfl
          intro B _
          exact d.componentOrientedCrossingCount_self orders shuffle B

/-- The complementary cross-component crossing set has even cardinality. -/
theorem QuarticWickDiagram.externalCrossingPairs_mod_two_eq_zero
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle) :
    (d.externalCrossingPairs orders shuffle).card % 2 = 0 := by
  have hparity := d.pairingInOrder_crossingCount_mod_two_eq_sum_components orders shuffle
  rw [d.crossingCount_eq_sum_add_card_externalCrossingPairs orders shuffle,
    Nat.add_mod] at hparity
  have hlt : (d.externalCrossingPairs orders shuffle).card % 2 < 2 :=
    Nat.mod_lt _ (by omega)
  omega

/-- Pairing weight factors over connected components for every component shuffle. -/
theorem QuarticWickDiagram.pairingInOrder_weight_eq_prod_components
    (s : Statistics) {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle) :
    (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).weight s =
      ∏ B : d.componentPartition.parts,
        ((d.restrictComponent B.2).pairingInOrder (orders B)).weight s := by
  exact d.pairingInOrder_weight_eq_prod_components_of_externalCrossingPairs_mod_two_eq_zero
    s orders shuffle (d.externalCrossingPairs_mod_two_eq_zero orders shuffle)

end SecondQuantization
