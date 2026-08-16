import LeanCondensedMatter.Combinatorics.PerfectPairing.CrossingParity

set_option linter.style.header false

/-!
# Crossing counts along a decomposition of the pairs

A decomposition of the normalized pairs of a pairing into components is an equivalence
`(Σ B, F B) ≃ pairing.NormalizedPair`. Reindexing the crossing count along it splits the count into
oriented contributions from ordered pairs of components.

Whenever the two orientations between distinct components cancel modulo two — which is what a block
structure on the ambient positions supplies — only the component-internal contributions survive the
parity. That statement is independent of what the components are, so it is stated here once.
-/

namespace Combinatorics

variable {n : ℕ} {ι : Type*} {F : ι → Type*} [∀ B, Fintype (F B)]

/-- Oriented crossing count from the pairs of component `B` to the pairs of component `C`. -/
noncomputable def Pairing.componentCrossingCount (pairing : Pairing n)
    (e : (Σ B : ι, F B) ≃ pairing.NormalizedPair) (B C : ι) : ℕ :=
  ∑ x : F B × F C, if Crosses (e ⟨B, x.1⟩).1 (e ⟨C, x.2⟩).1 then 1 else 0

/-- Unoriented geometric crossing count between two components. -/
noncomputable def Pairing.componentGeometricCrossingCount (pairing : Pairing n)
    (e : (Σ B : ι, F B) ≃ pairing.NormalizedPair) (B C : ι) : ℕ :=
  ∑ x : F B × F C,
    if Crosses (e ⟨B, x.1⟩).1 (e ⟨C, x.2⟩).1 ∨
      Crosses (e ⟨C, x.2⟩).1 (e ⟨B, x.1⟩).1 then 1 else 0

/-- The geometric crossing count between two components is the sum of its two orientations. -/
theorem Pairing.componentGeometricCrossingCount_eq_oriented_add (pairing : Pairing n)
    (e : (Σ B : ι, F B) ≃ pairing.NormalizedPair) (B C : ι) :
    pairing.componentGeometricCrossingCount e B C =
      pairing.componentCrossingCount e B C + pairing.componentCrossingCount e C B := by
  classical
  have hswap : pairing.componentCrossingCount e C B =
      ∑ x : F B × F C,
        if Crosses (e ⟨C, x.2⟩).1 (e ⟨B, x.1⟩).1 then 1 else 0 := by
    rw [Pairing.componentCrossingCount,
      ← Equiv.sum_comp (Equiv.prodComm (F B) (F C))]
    rfl
  rw [Pairing.componentGeometricCrossingCount, hswap,
    Pairing.componentCrossingCount, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hbc : Crosses (e ⟨B, x.1⟩).1 (e ⟨C, x.2⟩).1
  · have hcb : ¬ Crosses (e ⟨C, x.2⟩).1 (e ⟨B, x.1⟩).1 :=
      fun h => lt_asymm hbc.1 h.1
    simp [hbc, hcb]
  · simp [hbc]

/-- For distinct components, geometric crossing parity is the parity of endpoint-order inversions.

The endpoint equivalences may identify each component's pair endpoints with any finite component
position fiber. The compatibility hypothesis only requires that transporting such a position to the
ambient pairing agrees with selecting the corresponding endpoint of the decomposed normalized
pair. -/
theorem Pairing.componentGeometricCrossingCount_mod_two_eq_endpointInversionCount
    {P : ι → Type*} [∀ B, Fintype (P B)] (pairing : Pairing n)
    (e : (Σ B : ι, F B) ≃ pairing.NormalizedPair)
    (endpointEquiv : ∀ B, F B × Fin 2 ≃ P B)
    (position : ∀ B, P B → Fin (2 * n))
    (hposition : ∀ B p k,
      position B (endpointEquiv B (p, k)) = pairEndpointAt (e ⟨B, p⟩).1 k)
    (B C : ι) (hBC : B ≠ C) :
    pairing.componentGeometricCrossingCount e B C % 2 =
      (∑ p : P B, ∑ q : P C, if position C q < position B p then 1 else 0) % 2 := by
  classical
  have hparity :
      pairing.componentGeometricCrossingCount e B C % 2 =
        (∑ x : F B × F C,
          pairEndpointInversionCount (e ⟨B, x.1⟩).1 (e ⟨C, x.2⟩).1) % 2 := by
    rw [Pairing.componentGeometricCrossingCount]
    symm
    exact fintype_sum_mod_two_congr _ _ fun x => by
      have hPairNe : e ⟨B, x.1⟩ ≠ e ⟨C, x.2⟩ := by
        intro h
        exact hBC (congrArg Sigma.fst (e.injective h))
      have hEnds := pairing.normalizedPair_endpoints_ne_of_ne
        (e ⟨B, x.1⟩) (e ⟨C, x.2⟩) hPairNe
      have h := pairEndpointInversionCount_mod_two_eq_crossesIndicator
        (e ⟨B, x.1⟩).1 (e ⟨C, x.2⟩).1
        (pairing.pairs_normalized (e ⟨B, x.1⟩).2)
        (pairing.pairs_normalized (e ⟨C, x.2⟩).2)
        hEnds.1 hEnds.2.1 hEnds.2.2.1 hEnds.2.2.2
      split_ifs at h ⊢ <;> simpa using h
  have hsum :
      (∑ x : F B × F C,
        pairEndpointInversionCount (e ⟨B, x.1⟩).1 (e ⟨C, x.2⟩).1) =
        ∑ x : (F B × F C) × (Fin 2 × Fin 2),
          if position C (endpointEquiv C (x.1.2, x.2.2)) <
            position B (endpointEquiv B (x.1.1, x.2.1))
          then 1 else 0 := by
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    rw [pairEndpointInversionCount_eq_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hposition B p i, hposition C q j]
  let endpointPairEquiv :
      ((F B × F C) × (Fin 2 × Fin 2)) ≃ P B × P C :=
    (Equiv.prodProdProdComm _ _ _ _).trans
      (Equiv.prodCongr (endpointEquiv B) (endpointEquiv C))
  have hreindex :
      (∑ x : (F B × F C) × (Fin 2 × Fin 2),
        if position C (endpointEquiv C (x.1.2, x.2.2)) <
          position B (endpointEquiv B (x.1.1, x.2.1))
        then 1 else 0) =
        ∑ x : P B × P C,
          if position C x.2 < position B x.1 then 1 else 0 := by
    refine Fintype.sum_equiv endpointPairEquiv
      (fun x => if position C (endpointEquiv C (x.1.2, x.2.2)) <
        position B (endpointEquiv B (x.1.1, x.2.1)) then 1 else 0)
      (fun x => if position C x.2 < position B x.1 then 1 else 0) ?_
    intro x
    rfl
  calc
    pairing.componentGeometricCrossingCount e B C % 2 =
        (∑ x : F B × F C,
          pairEndpointInversionCount (e ⟨B, x.1⟩).1 (e ⟨C, x.2⟩).1) % 2 := hparity
    _ = (∑ x : (F B × F C) × (Fin 2 × Fin 2),
          if position C (endpointEquiv C (x.1.2, x.2.2)) <
            position B (endpointEquiv B (x.1.1, x.2.1))
          then 1 else 0) % 2 := by rw [hsum]
    _ = (∑ x : P B × P C,
          if position C x.2 < position B x.1 then 1 else 0) % 2 := by rw [hreindex]
    _ = (∑ p : P B, ∑ q : P C,
          if position C q < position B p then 1 else 0) % 2 := by
      rw [Fintype.sum_prod_type]

/-- The crossing count is the double sum of the oriented component crossing counts. -/
theorem Pairing.crossingCount_eq_sum_componentCrossingCount [Fintype ι] (pairing : Pairing n)
    (e : (Σ B : ι, F B) ≃ pairing.NormalizedPair) :
    pairing.crossingCount = ∑ B : ι, ∑ C : ι, pairing.componentCrossingCount e B C := by
  classical
  let sigmaProductEquiv :
      (Σ BC : ι × ι, F BC.1 × F BC.2) ≃ (Σ B : ι, F B) × (Σ C : ι, F C) := {
    toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
    invFun x := ⟨(x.1.1, x.2.1), (x.1.2, x.2.2)⟩
    left_inv := by rintro ⟨⟨B, C⟩, p, q⟩; rfl
    right_inv := by rintro ⟨⟨B, p⟩, ⟨C, q⟩⟩; rfl }
  rw [pairing.crossingCount_eq_sum_crosses,
    ← Equiv.sum_comp (sigmaProductEquiv.trans (Equiv.prodCongr e e)),
    Fintype.sum_sigma, Fintype.sum_prod_type]
  rfl

/-- When the two orientations between distinct components cancel modulo two, the crossing count has
the parity of the sum of the component-internal crossing counts. -/
theorem Pairing.crossingCount_mod_two_eq_sum_componentCrossingCount [Fintype ι]
    (pairing : Pairing n) (e : (Σ B : ι, F B) ≃ pairing.NormalizedPair)
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

end Combinatorics
