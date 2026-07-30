import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentPairs
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentPairValue

set_option linter.style.header false

/-!
# Component-local pair equivalence and pair-product reindexing

The component ordered-leg embeddings assemble to an equivalence from the sigma type of all
component-local ordered legs to the assembled global ordered-leg enumeration. Partner compatibility
then upgrades this to an equivalence between component-local normalized pairs and the normalized
pairs of the assembled global pairing. Products over global pairs can therefore be reindexed as an
iterated product over components and local pairs.
-/

namespace SecondQuantization

variable {Mode : Type*} {N : ℕ}

/-- Move a fiberwise subtype through a sigma type. -/
private def sigmaSubtypeFiberwiseEquiv {ι : Type*} {α : ι → Type*}
    (p : ∀ i, α i → Prop) :
    (Σ i, {x : α i // p i x}) ≃ {x : Σ i, α i // p x.1 x.2} where
  toFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  invFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Pairs drawn from a common fiber are equivalent to pairs whose fiber labels agree. -/
private def sigmaFiberPairEquiv {ι α : Type*} (f : α → ι) :
    (Σ i, {x : α // f x = i} × {x : α // f x = i}) ≃
      {p : α × α // f p.1 = f p.2} where
  toFun x :=
    ⟨(x.2.1.1, x.2.2.1), x.2.1.2.trans x.2.2.2.symm⟩
  invFun p :=
    ⟨f p.1.1, ⟨⟨p.1.1, rfl⟩, ⟨p.1.2, p.2.symm⟩⟩⟩
  left_inv := by
    rintro ⟨i, ⟨⟨a, ha⟩, ⟨b, hb⟩⟩⟩
    apply Sigma.ext ha
    apply heq_of_eq
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      rfl
  right_inv := by
    rintro ⟨⟨a, b⟩, hab⟩
    apply Subtype.ext
    rfl

/-- The normalized ordered pairs of one restricted component. -/
abbrev QuarticWickDiagram.LocalOrderedPair {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (orders : d.ComponentVertexOrders)
    (B : d.componentPartition.parts) :=
  {pr : Fin (2 * (2 * (B : Finset (Fin N)).card)) ×
      Fin (2 * (2 * (B : Finset (Fin N)).card)) //
    pr ∈ ((d.restrictComponent B.2).pairingInOrder (orders B)).pairs}

/-- The normalized ordered pairs in the assembled global order. -/
abbrev QuarticWickDiagram.GlobalOrderedPair {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (orders : d.ComponentVertexOrders)
    (shuffle : d.ComponentShuffle) :=
  {pr : Fin (2 * (2 * S.card)) × Fin (2 * (2 * S.card)) //
    pr ∈ (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).pairs}

/-- All component-local ordered legs, assembled by a component shuffle, are equivalent to the global
ordered-leg enumeration. -/
noncomputable def QuarticWickDiagram.componentOrderedLegEquiv {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (shuffle : d.ComponentShuffle) :
    (Σ B : d.componentPartition.parts,
      Fin (2 * (2 * (B : Finset (Fin N)).card))) ≃ Fin (2 * (2 * S.card)) :=
  (Equiv.sigmaCongrRight fun B : d.componentPartition.parts =>
      orderedQuarticLegEquiv (B : Finset (Fin N)).card).trans
    (((Equiv.sigmaProdDistrib
        (fun B : d.componentPartition.parts => Fin (B : Finset (Fin N)).card)
        (Fin 4)).symm).trans
      ((Equiv.prodCongr shuffle.slotEquiv (Equiv.refl (Fin 4))).trans
        (orderedQuarticLegEquiv S.card).symm))

@[simp]
theorem QuarticWickDiagram.componentOrderedLegEquiv_apply {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts)
    (p : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    d.componentOrderedLegEquiv shuffle ⟨B, p⟩ = d.componentOrderedLeg shuffle B p :=
  rfl

/-- The legs of one component are equivalent to the fiber of global legs assigned to it. -/
private noncomputable def QuarticWickDiagram.componentOrderedLegFiberEquiv
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (shuffle : d.ComponentShuffle) (B : d.componentPartition.parts) :
    Fin (2 * (2 * (B : Finset (Fin N)).card)) ≃
      {p : Fin (2 * (2 * S.card)) //
        ((d.componentOrderedLegEquiv shuffle).symm p).1 = B} :=
  (Equiv.sigmaSubtype B).symm.trans
    ((d.componentOrderedLegEquiv shuffle).subtypeEquiv (by
      intro x
      simp))

@[simp]
private theorem QuarticWickDiagram.componentOrderedLegFiberEquiv_apply
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (shuffle : d.ComponentShuffle) (B : d.componentPartition.parts)
    (p : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    (d.componentOrderedLegFiberEquiv shuffle B p).1 =
      d.componentOrderedLeg shuffle B p :=
  rfl

/-- The product of two component-local legs is the subtype of global leg pairs whose inverse images
belong to the same component. -/
private noncomputable def QuarticWickDiagram.componentOrderedLegPairEquiv
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (shuffle : d.ComponentShuffle) :
    (Σ B : d.componentPartition.parts,
      Fin (2 * (2 * (B : Finset (Fin N)).card)) ×
        Fin (2 * (2 * (B : Finset (Fin N)).card))) ≃
      {pr : Fin (2 * (2 * S.card)) × Fin (2 * (2 * S.card)) //
        ((d.componentOrderedLegEquiv shuffle).symm pr.1).1 =
          ((d.componentOrderedLegEquiv shuffle).symm pr.2).1} :=
  (Equiv.sigmaCongrRight fun B : d.componentPartition.parts =>
      Equiv.prodCongr (d.componentOrderedLegFiberEquiv shuffle B)
        (d.componentOrderedLegFiberEquiv shuffle B)).trans
    (sigmaFiberPairEquiv fun p : Fin (2 * (2 * S.card)) =>
      ((d.componentOrderedLegEquiv shuffle).symm p).1)

@[simp]
private theorem QuarticWickDiagram.componentOrderedLegPairEquiv_apply
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (shuffle : d.ComponentShuffle) (B : d.componentPartition.parts)
    (a b : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    (d.componentOrderedLegPairEquiv shuffle ⟨B, (a, b)⟩).1 =
      (d.componentOrderedLeg shuffle B a,
        d.componentOrderedLeg shuffle B b) :=
  rfl

/-- Package the local pair predicates as one subtype of a sigma type. -/
private def QuarticWickDiagram.localOrderedPairSigmaEquiv
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) :
    (Σ B : d.componentPartition.parts, d.LocalOrderedPair orders B) ≃
      {x : Σ B : d.componentPartition.parts,
          Fin (2 * (2 * (B : Finset (Fin N)).card)) ×
            Fin (2 * (2 * (B : Finset (Fin N)).card)) //
        x.2 ∈ ((d.restrictComponent x.1.2).pairingInOrder (orders x.1)).pairs} :=
  sigmaSubtypeFiberwiseEquiv fun B pr =>
    pr ∈ ((d.restrictComponent B.2).pairingInOrder (orders B)).pairs

/-- Restrict the ambient component-pair equivalence to normalized pairing predicates. -/
private noncomputable def QuarticWickDiagram.componentPairSubtypeEquiv
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle) :
    {x : Σ B : d.componentPartition.parts,
        Fin (2 * (2 * (B : Finset (Fin N)).card)) ×
          Fin (2 * (2 * (B : Finset (Fin N)).card)) //
      x.2 ∈ ((d.restrictComponent x.1.2).pairingInOrder (orders x.1)).pairs} ≃
      {pr : {pr : Fin (2 * (2 * S.card)) × Fin (2 * (2 * S.card)) //
          ((d.componentOrderedLegEquiv shuffle).symm pr.1).1 =
            ((d.componentOrderedLegEquiv shuffle).symm pr.2).1} //
        pr.1 ∈ (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).pairs} :=
  (d.componentOrderedLegPairEquiv shuffle).subtypeEquiv (by
    intro x
    rcases x with ⟨B, ⟨a, b⟩⟩
    exact (d.mem_pairingInOrder_pairs_componentOrderedLeg_iff
      orders shuffle B a b).symm)

/-- A normalized global pair has both endpoints in the same component fiber. -/
private theorem QuarticWickDiagram.globalOrderedPair_sameComponent
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (pr : d.GlobalOrderedPair orders shuffle) :
    ((d.componentOrderedLegEquiv shuffle).symm pr.1.1).1 =
      ((d.componentOrderedLegEquiv shuffle).symm pr.1.2).1 := by
  let x := (d.componentOrderedLegEquiv shuffle).symm pr.1.1
  let localB := ((d.restrictComponent x.1.2).pairingInOrder (orders x.1)).partner x.2
  have ha : d.componentOrderedLeg shuffle x.1 x.2 = pr.1.1 := by
    simpa only [d.componentOrderedLegEquiv_apply] using
      (d.componentOrderedLegEquiv shuffle).apply_symm_apply pr.1.1
  have hpr := pr.2
  rw [Common.BlochDeDominicis.Pairing.mem_pairs_iff] at hpr
  have hb : d.componentOrderedLeg shuffle x.1 localB = pr.1.2 := by
    calc
      d.componentOrderedLeg shuffle x.1 localB =
          (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).partner
            (d.componentOrderedLeg shuffle x.1 x.2) :=
        (d.pairingInOrder_partner_componentOrderedLeg
          orders shuffle x.1 x.2).symm
      _ = (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).partner pr.1.1 := by
        rw [ha]
      _ = pr.1.2 := hpr.2
  change x.1 = ((d.componentOrderedLegEquiv shuffle).symm pr.1.2).1
  rw [← hb, ← d.componentOrderedLegEquiv_apply]
  exact (congrArg Sigma.fst
    ((d.componentOrderedLegEquiv shuffle).symm_apply_apply ⟨x.1, localB⟩)).symm

/-- Forget the redundant same-component witness on a normalized global pair. -/
private def QuarticWickDiagram.globalOrderedPairSubtypeEquiv
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle) :
    {pr : {pr : Fin (2 * (2 * S.card)) × Fin (2 * (2 * S.card)) //
        ((d.componentOrderedLegEquiv shuffle).symm pr.1).1 =
          ((d.componentOrderedLegEquiv shuffle).symm pr.2).1} //
      pr.1 ∈ (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).pairs} ≃
      d.GlobalOrderedPair orders shuffle where
  toFun pr := ⟨pr.1.1, pr.2⟩
  invFun pr := ⟨⟨pr.1, d.globalOrderedPair_sameComponent orders shuffle pr⟩, pr.2⟩
  left_inv pr := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv pr := by
    apply Subtype.ext
    rfl

/-- Component-local normalized pairs are equivalent to the normalized pairs of the assembled global
pairing by restricting the ambient product equivalence to the pairing predicates. -/
noncomputable def QuarticWickDiagram.componentPairEquiv {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (orders : d.ComponentVertexOrders)
    (shuffle : d.ComponentShuffle) :
    (Σ B : d.componentPartition.parts, d.LocalOrderedPair orders B) ≃
      d.GlobalOrderedPair orders shuffle :=
  (d.localOrderedPairSigmaEquiv orders).trans
    ((d.componentPairSubtypeEquiv orders shuffle).trans
      (d.globalOrderedPairSubtypeEquiv orders shuffle))

/-- Map a component-local normalized pair to its assembled global normalized pair. -/
noncomputable def QuarticWickDiagram.componentPairToGlobal {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (orders : d.ComponentVertexOrders)
    (shuffle : d.ComponentShuffle) :
    (Σ B : d.componentPartition.parts, d.LocalOrderedPair orders B) →
      d.GlobalOrderedPair orders shuffle :=
  d.componentPairEquiv orders shuffle

/-- The component-pair map is injective. -/
theorem QuarticWickDiagram.componentPairToGlobal_injective {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (orders : d.ComponentVertexOrders)
    (shuffle : d.ComponentShuffle) :
    Function.Injective (d.componentPairToGlobal orders shuffle) :=
  (d.componentPairEquiv orders shuffle).injective

/-- Every assembled global normalized pair comes from a component-local normalized pair. -/
theorem QuarticWickDiagram.componentPairToGlobal_surjective {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (orders : d.ComponentVertexOrders)
    (shuffle : d.ComponentShuffle) :
    Function.Surjective (d.componentPairToGlobal orders shuffle) :=
  (d.componentPairEquiv orders shuffle).surjective

@[simp]
theorem QuarticWickDiagram.componentPairEquiv_apply {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (orders : d.ComponentVertexOrders)
    (shuffle : d.ComponentShuffle) (B : d.componentPartition.parts)
    (pr : d.LocalOrderedPair orders B) :
    (d.componentPairEquiv orders shuffle ⟨B, pr⟩).1 =
      (d.componentOrderedLeg shuffle B pr.1.1,
        d.componentOrderedLeg shuffle B pr.1.2) :=
  rfl

/-- Reindex a product over assembled global normalized pairs as an iterated product over components
and component-local normalized pairs. -/
theorem QuarticWickDiagram.prod_componentPairs {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (orders : d.ComponentVertexOrders)
    (shuffle : d.ComponentShuffle) {M : Type*} [CommMonoid M]
    (F : d.GlobalOrderedPair orders shuffle → M) :
    (∏ pr, F pr) =
      ∏ B : d.componentPartition.parts,
        ∏ pr : d.LocalOrderedPair orders B,
          F (d.componentPairEquiv orders shuffle ⟨B, pr⟩) := by
  classical
  calc
    (∏ pr, F pr) =
        ∏ x : Σ B : d.componentPartition.parts, d.LocalOrderedPair orders B,
          F (d.componentPairEquiv orders shuffle x) := by
      refine Fintype.prod_equiv (d.componentPairEquiv orders shuffle).symm F
        (fun x => F (d.componentPairEquiv orders shuffle x)) ?_
      intro pr
      simp
    _ = ∏ B : d.componentPartition.parts,
        ∏ pr : d.LocalOrderedPair orders B,
          F (d.componentPairEquiv orders shuffle ⟨B, pr⟩) :=
      Fintype.prod_sigma _

section Fermionic

variable [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

/-- The product of pair values in an assembled global order is the iterated product of the
component-local pair values. -/
theorem QuarticWickDiagram.prod_orderedQuarticPairValue_eq_prod_components
    (ε : Mode → ℝ) (β : ℝ) {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (orders : d.ComponentVertexOrders)
    (shuffle : d.ComponentShuffle) (τ : Fin S.card → ℝ) :
    (∏ pr : d.GlobalOrderedPair orders shuffle,
      orderedQuarticPairValue ε β d (d.assembleVertexOrder orders shuffle) τ pr.1.1 pr.1.2) =
      ∏ B : d.componentPartition.parts,
        ∏ pr : d.LocalOrderedPair orders B,
          orderedQuarticPairValue ε β (d.restrictComponent B.2) (orders B)
            (d.componentTimeAssignment shuffle τ B) pr.1.1 pr.1.2 := by
  rw [d.prod_componentPairs orders shuffle]
  apply Fintype.prod_congr
  intro B
  apply Fintype.prod_congr
  intro pr
  simpa using
    (orderedQuarticPairValue_componentOrderedLeg
      ε β d orders shuffle τ B pr.1.1 pr.1.2)

/-- The pair-value product factorization in the same nested-Finset form used by
`QuarticWickDiagram.contractionIntegrand`. -/
theorem QuarticWickDiagram.prod_orderedQuarticPairValue_pairs_eq_prod_components
    (ε : Mode → ℝ) (β : ℝ) {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (orders : d.ComponentVertexOrders)
    (shuffle : d.ComponentShuffle) (τ : Fin S.card → ℝ) :
    (∏ pr ∈ (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).pairs,
      orderedQuarticPairValue ε β d (d.assembleVertexOrder orders shuffle) τ pr.1 pr.2) =
      ∏ B : d.componentPartition.parts,
        ∏ pr ∈ ((d.restrictComponent B.2).pairingInOrder (orders B)).pairs,
          orderedQuarticPairValue ε β (d.restrictComponent B.2) (orders B)
            (d.componentTimeAssignment shuffle τ B) pr.1 pr.2 := by
  classical
  calc
    (∏ pr ∈ (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).pairs,
        orderedQuarticPairValue ε β d (d.assembleVertexOrder orders shuffle) τ pr.1 pr.2) =
        (∏ pr : d.GlobalOrderedPair orders shuffle,
          orderedQuarticPairValue ε β d (d.assembleVertexOrder orders shuffle)
            τ pr.1.1 pr.1.2) :=
      Finset.prod_subtype _ (fun _ => Iff.rfl) _
    _ = ∏ B : d.componentPartition.parts,
        ∏ pr : d.LocalOrderedPair orders B,
          orderedQuarticPairValue ε β (d.restrictComponent B.2) (orders B)
            (d.componentTimeAssignment shuffle τ B) pr.1.1 pr.1.2 :=
      d.prod_orderedQuarticPairValue_eq_prod_components ε β orders shuffle τ
    _ = ∏ B : d.componentPartition.parts,
        ∏ pr ∈ ((d.restrictComponent B.2).pairingInOrder (orders B)).pairs,
          orderedQuarticPairValue ε β (d.restrictComponent B.2) (orders B)
            (d.componentTimeAssignment shuffle τ B) pr.1 pr.2 := by
      apply Fintype.prod_congr
      intro B
      exact (Finset.prod_subtype
        ((d.restrictComponent B.2).pairingInOrder (orders B)).pairs
        (fun _ => Iff.rfl)
        (fun pr => orderedQuarticPairValue ε β (d.restrictComponent B.2) (orders B)
          (d.componentTimeAssignment shuffle τ B) pr.1 pr.2)).symm

end Fermionic

end SecondQuantization
