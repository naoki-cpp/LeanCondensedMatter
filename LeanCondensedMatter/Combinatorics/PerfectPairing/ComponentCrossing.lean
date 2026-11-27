import LeanCondensedMatter.Combinatorics.PerfectPairing.CrossingParity
import LeanCondensedMatter.Combinatorics.FiniteSumModEq
import LeanCondensedMatter.Combinatorics.Common.FintypeProduct
import LeanCondensedMatter.Combinatorics.Shuffle.FamilySlotShuffleInversions

set_option linter.style.header false

/-!
# Crossing counts along a decomposition of the pairs

A decomposition of the normalized pairs of a pairing into components is an equivalence
`(Σ B, F B) ≃ pairing.NormalizedPair`. Reindexing the crossing count along it splits the count into
oriented contributions from ordered pairs of components.

When component endpoints form a family shuffle, the residual crossing parity equals the ordered
inter-block inversion parity. Only when the two orientations between distinct components cancel
modulo two do the component-internal contributions alone determine the global parity.
-/

namespace Combinatorics

variable {α ι : Type*} [Fintype α] [LinearOrder α]
  {F : ι → Type*} [∀ B, Fintype (F B)]

/-- Oriented crossing count from the pairs of component `B` to the pairs of component `C`. -/
noncomputable def PairingOn.componentCrossingCount (pairing : PairingOn α)
    (e : (Σ B : ι, F B) ≃ pairing.NormalizedPair) (B C : ι) : ℕ :=
  ∑ x : F B × F C, if Crosses (e ⟨B, x.1⟩).1 (e ⟨C, x.2⟩).1 then 1 else 0

/-- Unoriented geometric crossing count between two components. -/
noncomputable def PairingOn.componentGeometricCrossingCount (pairing : PairingOn α)
    (e : (Σ B : ι, F B) ≃ pairing.NormalizedPair) (B C : ι) : ℕ :=
  ∑ x : F B × F C,
    if Crosses (e ⟨B, x.1⟩).1 (e ⟨C, x.2⟩).1 ∨
      Crosses (e ⟨C, x.2⟩).1 (e ⟨B, x.1⟩).1 then 1 else 0

/-- The geometric crossing count between two components is the sum of its two orientations. -/
theorem PairingOn.componentGeometricCrossingCount_eq_oriented_add (pairing : PairingOn α)
    (e : (Σ B : ι, F B) ≃ pairing.NormalizedPair) (B C : ι) :
    pairing.componentGeometricCrossingCount e B C =
      pairing.componentCrossingCount e B C + pairing.componentCrossingCount e C B := by
  simpa only [PairingOn.componentGeometricCrossingCount, PairingOn.componentCrossingCount,
    Fintype.sum_prod_type] using
    (sum_sum_crosses_oriented_add (fun p : F B => (e ⟨B, p⟩).1)
      (fun q : F C => (e ⟨C, q⟩).1)).symm

/-- The geometric crossing count between two components does not depend on their order. -/
theorem PairingOn.componentGeometricCrossingCount_comm (pairing : PairingOn α)
    (e : (Σ B : ι, F B) ≃ pairing.NormalizedPair) (B C : ι) :
    pairing.componentGeometricCrossingCount e B C =
      pairing.componentGeometricCrossingCount e C B := by
  rw [pairing.componentGeometricCrossingCount_eq_oriented_add e B C,
    pairing.componentGeometricCrossingCount_eq_oriented_add e C B]
  exact Nat.add_comm _ _

/-- For distinct components, geometric crossing parity is the parity of endpoint-order inversions.

The endpoint equivalences may identify each component's pair endpoints with any finite component
position fiber. The compatibility hypothesis only requires that transporting such a position to the
ambient pairing agrees with selecting the corresponding endpoint of the decomposed normalized
pair. -/
theorem PairingOn.componentGeometricCrossingCount_mod_two_eq_endpointInversionCount
    {P : ι → Type*} [∀ B, Fintype (P B)] (pairing : PairingOn α)
    (e : (Σ B : ι, F B) ≃ pairing.NormalizedPair)
    (endpointEquiv : ∀ B, F B × Fin 2 ≃ P B)
    (position : ∀ B, P B → α)
    (hposition : ∀ B p k,
      position B (endpointEquiv B (p, k)) = pairEndpointAt (e ⟨B, p⟩).1 k)
    (B C : ι) (hBC : B ≠ C) :
    pairing.componentGeometricCrossingCount e B C % 2 =
      (∑ p : P B, ∑ q : P C, if position C q < position B p then 1 else 0) % 2 := by
  exact pairing.sum_geometricCrossings_mod_two_eq_positionInversions
    (fun p => e ⟨B, p⟩) (fun q => e ⟨C, q⟩)
    (fun _ _ h => hBC (congrArg Sigma.fst (e.injective h)))
    (endpointEquiv B) (endpointEquiv C) (position B) (position C)
    (fun p => Or.inl (Prod.ext (hposition B p 0).symm (hposition B p 1).symm))
    (fun q => Or.inl (Prod.ext (hposition C q 0).symm (hposition C q 1).symm))

/-- A geometric crossing count between distinct components is even when one component's
positions form even-sized fibers and their order relative to the other component is constant
within each fiber. The result is independent of how the local pairing is represented. -/
theorem PairingOn.componentGeometricCrossingCount_mod_two_eq_zero_of_even_fiber
    {P : ι → Type*} [∀ B, Finite (P B)] (pairing : PairingOn α)
    (e : (Σ B : ι, F B) ≃ pairing.NormalizedPair)
    (endpointEquiv : ∀ B, F B × Fin 2 ≃ P B)
    (position : ∀ B, P B → α)
    (hposition : ∀ B p k,
      position B (endpointEquiv B (p, k)) = pairEndpointAt (e ⟨B, p⟩).1 k)
    (B C : ι) (hBC : B ≠ C)
    {β γ : Type*} [Finite β] [Fintype γ]
    (fiber : P C ≃ β × γ) (reference : β → P C)
    (huniform : ∀ (p : P B) (q : P C),
      (position C q < position B p) =
        (position C (reference (fiber q).1) < position B p))
    (hcard : 2 ∣ Fintype.card γ) :
    pairing.componentGeometricCrossingCount e B C % 2 = 0 := by
  classical
  letI : (D : ι) → Fintype (P D) := fun D => Fintype.ofFinite (P D)
  letI : Fintype β := Fintype.ofFinite β
  rw [pairing.componentGeometricCrossingCount_mod_two_eq_endpointInversionCount
    e endpointEquiv position hposition B C hBC]
  apply Nat.mod_eq_zero_of_dvd
  refine Finset.dvd_sum fun p _ => ?_
  have hsum :
      (∑ q : P C, if position C q < position B p then 1 else 0) =
        ∑ q : P C, (fun v : β =>
          if position C (reference v) < position B p then 1 else 0) (fiber q).1 := by
    apply Finset.sum_congr rfl
    intro q _
    simpa only [huniform p q]
  rw [hsum]
  exact Fintype.dvd_sum_equiv_fst_of_dvd_card fiber
    (fun v : β => if position C (reference v) < position B p then 1 else 0) hcard

/-- The diagonal component crossing count agrees with a local pairing's crossing count when
the component equivalence maps local normalized pairs by a strictly monotone ambient position
map. -/
theorem PairingOn.componentCrossingCount_self_eq
    {δ : Type*} [Fintype δ] [LinearOrder δ]
    (pairing : PairingOn α) (localPairing : PairingOn δ)
    (e : (Σ B : ι, F B) ≃ pairing.NormalizedPair) (B : ι)
    (localEquiv : localPairing.NormalizedPair ≃ F B)
    (position : δ → α) (hmono : StrictMono position)
    (hpair : ∀ pr : localPairing.NormalizedPair,
      (e ⟨B, localEquiv pr⟩).1 =
        (position pr.1.1, position pr.1.2)) :
    pairing.componentCrossingCount e B B = localPairing.crossingCount := by
  rw [PairingOn.componentCrossingCount, Fintype.sum_prod_type]
  exact localPairing.sum_sum_crosses_map_eq_crossingCount position hmono
    (fun p : F B => (e ⟨B, p⟩).1) localEquiv.symm
    (fun p => by simpa only [Equiv.apply_symm_apply] using hpair (localEquiv.symm p))

/-- The crossing count is the double sum of the oriented component crossing counts. -/
theorem PairingOn.crossingCount_eq_sum_componentCrossingCount [Fintype ι] (pairing : PairingOn α)
    (e : (Σ B : ι, F B) ≃ pairing.NormalizedPair) :
    pairing.crossingCount = ∑ B : ι, ∑ C : ι, pairing.componentCrossingCount e B C := by
  classical
  rw [pairing.crossingCount_eq_sum_sum_crosses_of_equiv e, Fintype.sum_sigma]
  simp_rw [Fintype.sum_sigma]
  simp only [PairingOn.componentCrossingCount, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun B _ => Finset.sum_comm


open Classical in
/-- The total oriented crossing count between distinct components. -/
noncomputable def PairingOn.interComponentCrossingCount [Fintype ι] (pairing : PairingOn α)
    (e : (Σ B : ι, F B) ≃ pairing.NormalizedPair) : ℕ :=
  ∑ BC ∈ (Finset.univ : Finset ι).offDiag,
    pairing.componentCrossingCount e BC.1 BC.2

/-- The residual crossing parity of a pairing decomposition is the ordered block-inversion parity
of any family shuffle that agrees with its pair endpoints. The block order remains explicit. -/
theorem Pairing.interComponentCrossingCount_mod_two_eq_orderedBlockInversionCount
    {n : ℕ} [Fintype ι] {size : ι → ℕ} (pairing : Pairing n)
    (e : (Σ B : ι, F B) ≃ pairing.NormalizedPair)
    (endpointEquiv : ∀ B, F B × Fin 2 ≃ Fin (size B))
    (shuffle : FamilySlotShuffleTo size (2 * n))
    (hposition : ∀ B p k,
      shuffle.slotEquiv ⟨B, endpointEquiv B (p, k)⟩ = pairEndpointAt (e ⟨B, p⟩).1 k)
    (blockOrder : ι ≃ Fin (Fintype.card ι)) :
    pairing.interComponentCrossingCount e % 2 =
      shuffle.orderedBlockInversionCount blockOrder % 2 := by
  classical
  have hpair : ∀ B C : ι, B ≠ C →
      Nat.ModEq 2
        (pairing.componentCrossingCount e B C + pairing.componentCrossingCount e C B)
        (shuffle.blockInversionCount B C) := by
    intro B C hBC
    change (pairing.componentCrossingCount e B C +
      pairing.componentCrossingCount e C B) % 2 = shuffle.blockInversionCount B C % 2
    rw [← pairing.componentGeometricCrossingCount_eq_oriented_add e B C,
      shuffle.blockInversionCount_of_ne hBC]
    exact pairing.componentGeometricCrossingCount_mod_two_eq_endpointInversionCount
      e endpointEquiv (fun B p => shuffle.slotEquiv ⟨B, p⟩) hposition B C hBC
  exact finset_sum_offDiag_modEq_of_pair_add_modEq_of_order
    2 (Finset.univ : Finset ι) blockOrder
    (fun _ _ _ _ h => blockOrder.injective h)
    (fun B C => pairing.componentCrossingCount e B C)
    (fun B C => shuffle.blockInversionCount B C)
    (fun B _ C _ hBC => hpair B C hBC)

/-- The crossing count of a pairing assembled from order-preserving local pairings is
the sum of the local crossing counts and the residual crossings between components.
The normalized-pair decomposition may use arbitrary component fibers. -/
theorem PairingOn.crossingCount_eq_sum_localCrossingCount_add_inter [Fintype ι]
    {δ : ι → Type*} [∀ B, Fintype (δ B)] [∀ B, LinearOrder (δ B)]
    (pairing : PairingOn α) (localPairing : ∀ B, PairingOn (δ B))
    (e : (Σ B : ι, F B) ≃ pairing.NormalizedPair)
    (localEquiv : ∀ B, (localPairing B).NormalizedPair ≃ F B)
    (position : ∀ B, δ B → α)
    (hmono : ∀ B, StrictMono (position B))
    (hpair : ∀ B (pr : (localPairing B).NormalizedPair),
      (e ⟨B, localEquiv B pr⟩).1 =
        (position B pr.1.1, position B pr.1.2)) :
    pairing.crossingCount =
      (∑ B : ι, (localPairing B).crossingCount) +
        pairing.interComponentCrossingCount e := by
  calc
    pairing.crossingCount =
        (∑ B : ι, pairing.componentCrossingCount e B B) +
          pairing.interComponentCrossingCount e := by
      classical
      rw [pairing.crossingCount_eq_sum_componentCrossingCount e]
      simp_rw [← Finset.sum_product']
      rw [← Finset.diag_union_offDiag,
        Finset.sum_union (Finset.disjoint_diag_offDiag _), Finset.sum_diag]
      rfl
    _ = (∑ B : ι, (localPairing B).crossingCount) +
        pairing.interComponentCrossingCount e := by
      congr 1
      apply Finset.sum_congr rfl
      intro B _
      exact pairing.componentCrossingCount_self_eq (localPairing B) e B
        (localEquiv B) (position B) (hmono B) (hpair B)

/-- When the two orientations between distinct components cancel modulo two, the crossing count has
the parity of the sum of the component-internal crossing counts. -/
theorem PairingOn.crossingCount_mod_two_eq_sum_componentCrossingCount [Fintype ι]
    (pairing : PairingOn α) (e : (Σ B : ι, F B) ≃ pairing.NormalizedPair)
    (hpair : ∀ B C : ι, B ≠ C →
      (pairing.componentCrossingCount e B C + pairing.componentCrossingCount e C B) % 2 = 0) :
    pairing.crossingCount % 2 = (∑ B : ι, pairing.componentCrossingCount e B B) % 2 := by
  rw [pairing.crossingCount_eq_sum_componentCrossingCount e]
  exact fintype_sum_sum_modEq_diag_of_pair_add_modEq_zero 2
    (fun B C => pairing.componentCrossingCount e B C)
    (fun B C hBC => by
      change (pairing.componentCrossingCount e B C +
        pairing.componentCrossingCount e C B) % 2 = 0 % 2
      simpa using hpair B C hBC)

/-- If geometric crossing counts between distinct components are even, the crossing count
has the same parity as the sum of the component-internal crossing counts. -/
theorem PairingOn.crossingCount_mod_two_eq_sum_componentCrossingCount_of_geometric_even
    [Fintype ι] (pairing : PairingOn α)
    (e : (Σ B : ι, F B) ≃ pairing.NormalizedPair)
    (hEven : ∀ B C : ι, B ≠ C →
      pairing.componentGeometricCrossingCount e B C % 2 = 0) :
    pairing.crossingCount % 2 =
      (∑ B : ι, pairing.componentCrossingCount e B B) % 2 := by
  apply pairing.crossingCount_mod_two_eq_sum_componentCrossingCount e
  intro B C hBC
  rw [← pairing.componentGeometricCrossingCount_eq_oriented_add e B C]
  exact hEven B C hBC

end Combinatorics
