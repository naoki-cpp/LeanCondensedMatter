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

variable {Mode : Type*} {N : ℕ}

private theorem crosses_asymm {n : ℕ}
    (p q : Fin (2 * n) × Fin (2 * n))
    (hpq : Common.BlochDeDominicis.Crosses p q) :
    ¬ Common.BlochDeDominicis.Crosses q p := by
  intro hqp
  exact lt_asymm hpq.1 hqp.1

/-- Oriented crossing count from pairs in component `B` to pairs in component `C`. -/
noncomputable def QuarticWickDiagram.componentOrientedCrossingCount
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B C : d.componentPartition.parts) : ℕ :=
  ∑ x : d.LocalOrderedPair orders B × d.LocalOrderedPair orders C,
    if Common.BlochDeDominicis.Crosses
        (d.componentPairEquiv orders shuffle ⟨B, x.1⟩).1
        (d.componentPairEquiv orders shuffle ⟨C, x.2⟩).1
    then 1 else 0

/-- For distinct components, the unoriented geometric crossing count is the sum of its two
orientations. -/
theorem QuarticWickDiagram.componentGeometricCrossingCount_eq_oriented_add
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B C : d.componentPartition.parts) (_hBC : B ≠ C) :
    d.componentGeometricCrossingCount orders shuffle B C =
      d.componentOrientedCrossingCount orders shuffle B C +
        d.componentOrientedCrossingCount orders shuffle C B := by
  classical
  let crossBC := fun p : d.LocalOrderedPair orders B =>
    fun q : d.LocalOrderedPair orders C =>
      Common.BlochDeDominicis.Crosses
        (d.componentPairEquiv orders shuffle ⟨B, p⟩).1
        (d.componentPairEquiv orders shuffle ⟨C, q⟩).1
  let crossCB := fun p : d.LocalOrderedPair orders B =>
    fun q : d.LocalOrderedPair orders C =>
      Common.BlochDeDominicis.Crosses
        (d.componentPairEquiv orders shuffle ⟨C, q⟩).1
        (d.componentPairEquiv orders shuffle ⟨B, p⟩).1
  have hpoint : ∀ p q,
      (if crossBC p q ∨ crossCB p q then 1 else 0) =
        (if crossBC p q then 1 else 0) + (if crossCB p q then 1 else 0) := by
    intro p q
    by_cases hbc : crossBC p q
    · have hcb : ¬ crossCB p q := crosses_asymm _ _ hbc
      simp [hbc, hcb]
    · by_cases hcb : crossCB p q <;> simp [hbc, hcb]
  have hcomm :
      (∑ q : d.LocalOrderedPair orders C,
        ∑ p : d.LocalOrderedPair orders B,
          if crossCB p q then 1 else 0) =
        ∑ p : d.LocalOrderedPair orders B,
          ∑ q : d.LocalOrderedPair orders C,
            if crossCB p q then 1 else 0 :=
    Finset.sum_comm
  rw [QuarticWickDiagram.componentGeometricCrossingCount,
    QuarticWickDiagram.componentOrientedCrossingCount,
    QuarticWickDiagram.componentOrientedCrossingCount,
    Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
  change (∑ p, ∑ q, if crossBC p q ∨ crossCB p q then 1 else 0) = _
  rw [hcomm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  exact hpoint p q

/-- The diagonal oriented crossing count is the local crossing count of that component. -/
theorem QuarticWickDiagram.componentOrientedCrossingCount_self
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts) :
    d.componentOrientedCrossingCount orders shuffle B B =
      ((d.restrictComponent B.2).pairingInOrder (orders B)).crossingCount := by
  classical
  rw [QuarticWickDiagram.componentOrientedCrossingCount, Fintype.sum_prod_type,
    Common.BlochDeDominicis.Pairing.crossingCount_eq_sum_sum_crosses]
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
  let productEquiv := Equiv.prodCongr pairEquiv pairEquiv
  rw [globalPairing.crossingCount_eq_sum_crosses,
    ← Equiv.sum_comp productEquiv, Fintype.sum_prod_type,
    Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro B _
  calc
    (∑ p : d.LocalOrderedPair orders B,
        ∑ y : Σ C : d.componentPartition.parts, d.LocalOrderedPair orders C,
          if Common.BlochDeDominicis.Crosses
              (productEquiv (⟨B, p⟩, y)).1.1
              (productEquiv (⟨B, p⟩, y)).2.1
          then 1 else 0) =
      ∑ p : d.LocalOrderedPair orders B,
        ∑ C : d.componentPartition.parts,
          ∑ q : d.LocalOrderedPair orders C,
            if Common.BlochDeDominicis.Crosses
                (d.componentPairEquiv orders shuffle ⟨B, p⟩).1
                (d.componentPairEquiv orders shuffle ⟨C, q⟩).1
            then 1 else 0 := by
              apply Finset.sum_congr rfl
              intro p _
              rw [Fintype.sum_sigma]
              rfl
    _ = ∑ C : d.componentPartition.parts,
        ∑ p : d.LocalOrderedPair orders B,
          ∑ q : d.LocalOrderedPair orders C,
            if Common.BlochDeDominicis.Crosses
                (d.componentPairEquiv orders shuffle ⟨B, p⟩).1
                (d.componentPairEquiv orders shuffle ⟨C, q⟩).1
            then 1 else 0 := by
              rw [Finset.sum_comm]
    _ = ∑ C : d.componentPartition.parts,
        d.componentOrientedCrossingCount orders shuffle B C := by
              apply Finset.sum_congr rfl
              intro C _
              rw [QuarticWickDiagram.componentOrientedCrossingCount,
                Fintype.sum_prod_type]

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
          exact Common.BlochDeDominicis.fintype_sum_sum_mod_two_eq_diag_of_pair_add_mod_two_eq_zero
            (fun B C => d.componentOrientedCrossingCount orders shuffle B C)
            (fun B C hBC => by
              rw [← d.componentGeometricCrossingCount_eq_oriented_add
                orders shuffle B C hBC,
                d.componentGeometricCrossingCount_mod_two_eq_zero
                  orders shuffle B C hBC])
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
