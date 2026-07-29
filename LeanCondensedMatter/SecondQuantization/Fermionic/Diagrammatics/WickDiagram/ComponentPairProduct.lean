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

/-- Pull a constant product factor out of a dependent sigma type. -/
private def sigmaProdEquiv {ι : Type*} (A : ι → Type*) (C : Type*) :
    (Σ i : ι, A i × C) ≃ (Σ i : ι, A i) × C where
  toFun x := (⟨x.1, x.2.1⟩, x.2.2)
  invFun x := ⟨x.1.1, (x.1.2, x.2)⟩
  left_inv x := by rcases x with ⟨i, a, c⟩; rfl
  right_inv x := by rcases x with ⟨⟨i, a⟩, c⟩; rfl

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
    ((sigmaProdEquiv
        (fun B : d.componentPartition.parts => Fin (B : Finset (Fin N)).card)
        (Fin 4)).trans
      ((Equiv.prodCongr shuffle.slotEquiv (Equiv.refl (Fin 4))).trans
        (orderedQuarticLegEquiv S.card).symm))

@[simp]
theorem QuarticWickDiagram.componentOrderedLegEquiv_apply {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts)
    (p : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    d.componentOrderedLegEquiv shuffle ⟨B, p⟩ = d.componentOrderedLeg shuffle B p :=
  rfl

/-- Map a component-local normalized pair to its assembled global normalized pair. -/
noncomputable def QuarticWickDiagram.componentPairToGlobal {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (orders : d.ComponentVertexOrders)
    (shuffle : d.ComponentShuffle) :
    (Σ B : d.componentPartition.parts, d.LocalOrderedPair orders B) →
      d.GlobalOrderedPair orders shuffle :=
  fun x =>
    ⟨(d.componentOrderedLeg shuffle x.1 x.2.1.1,
        d.componentOrderedLeg shuffle x.1 x.2.1.2),
      (d.mem_pairingInOrder_pairs_componentOrderedLeg_iff
        orders shuffle x.1 x.2.1.1 x.2.1.2).2 x.2.2⟩

/-- The component-pair map is injective. -/
theorem QuarticWickDiagram.componentPairToGlobal_injective {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (orders : d.ComponentVertexOrders)
    (shuffle : d.ComponentShuffle) :
    Function.Injective (d.componentPairToGlobal orders shuffle) := by
  rintro ⟨B, ⟨⟨a, b⟩, hab⟩⟩ ⟨C, ⟨⟨c, e⟩, hce⟩⟩ hxy
  have hval := congrArg Subtype.val hxy
  change
    (d.componentOrderedLeg shuffle B a, d.componentOrderedLeg shuffle B b) =
      (d.componentOrderedLeg shuffle C c, d.componentOrderedLeg shuffle C e) at hval
  have hfst := congrArg Prod.fst hval
  have hfstEquiv :
      d.componentOrderedLegEquiv shuffle ⟨B, a⟩ =
        d.componentOrderedLegEquiv shuffle ⟨C, c⟩ := by
    simpa only [d.componentOrderedLegEquiv_apply] using hfst
  have hsigmaFst := (d.componentOrderedLegEquiv shuffle).injective hfstEquiv
  cases hsigmaFst
  have hsnd := congrArg Prod.snd hval
  have hsndEquiv :
      d.componentOrderedLegEquiv shuffle ⟨B, b⟩ =
        d.componentOrderedLegEquiv shuffle ⟨B, e⟩ := by
    simpa only [d.componentOrderedLegEquiv_apply] using hsnd
  have hsigmaSnd := (d.componentOrderedLegEquiv shuffle).injective hsndEquiv
  cases hsigmaSnd
  rfl

/-- Every assembled global normalized pair comes from a component-local normalized pair. -/
theorem QuarticWickDiagram.componentPairToGlobal_surjective {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (orders : d.ComponentVertexOrders)
    (shuffle : d.ComponentShuffle) :
    Function.Surjective (d.componentPairToGlobal orders shuffle) := by
  rintro ⟨⟨a, b⟩, hab⟩
  let x := (d.componentOrderedLegEquiv shuffle).symm a
  let B := x.1
  let localA := x.2
  let localPairing := (d.restrictComponent B.2).pairingInOrder (orders B)
  let localB := localPairing.partner localA
  have ha0 := (d.componentOrderedLegEquiv shuffle).apply_symm_apply a
  have hxeta : (⟨B, localA⟩ :
      Σ B : d.componentPartition.parts,
        Fin (2 * (2 * (B : Finset (Fin N)).card))) = x := by
    dsimp [B, localA]
  have ha : d.componentOrderedLeg shuffle B localA = a := by
    calc
      d.componentOrderedLeg shuffle B localA =
          d.componentOrderedLegEquiv shuffle ⟨B, localA⟩ := by simp
      _ = d.componentOrderedLegEquiv shuffle x := congrArg _ hxeta
      _ = a := ha0
  rw [Common.BlochDeDominicis.Pairing.mem_pairs_iff] at hab
  have hb : d.componentOrderedLeg shuffle B localB = b := by
    calc
      d.componentOrderedLeg shuffle B localB =
          (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).partner
            (d.componentOrderedLeg shuffle B localA) :=
        (d.pairingInOrder_partner_componentOrderedLeg orders shuffle B localA).symm
      _ = (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).partner a := by rw [ha]
      _ = b := hab.2
  have hglobal :
      (d.componentOrderedLeg shuffle B localA,
        d.componentOrderedLeg shuffle B localB) ∈
        (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).pairs := by
    rw [Common.BlochDeDominicis.Pairing.mem_pairs_iff]
    exact ⟨by simpa only [ha, hb] using hab.1, by simpa only [ha, hb] using hab.2⟩
  have hlocal : (localA, localB) ∈ localPairing.pairs :=
    (d.mem_pairingInOrder_pairs_componentOrderedLeg_iff
      orders shuffle B localA localB).1 hglobal
  refine ⟨⟨B, ⟨(localA, localB), hlocal⟩⟩, ?_⟩
  apply Subtype.ext
  exact Prod.ext ha hb

/-- Component-local normalized pairs are equivalent to the normalized pairs of the assembled global
pairing. -/
noncomputable def QuarticWickDiagram.componentPairEquiv {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (orders : d.ComponentVertexOrders)
    (shuffle : d.ComponentShuffle) :
    (Σ B : d.componentPartition.parts, d.LocalOrderedPair orders B) ≃
      d.GlobalOrderedPair orders shuffle :=
  Equiv.ofBijective (d.componentPairToGlobal orders shuffle)
    ⟨d.componentPairToGlobal_injective orders shuffle,
      d.componentPairToGlobal_surjective orders shuffle⟩

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
  have hglobal :
      (∏ pr : d.GlobalOrderedPair orders shuffle,
        orderedQuarticPairValue ε β d (d.assembleVertexOrder orders shuffle)
          τ pr.1.1 pr.1.2) =
        ∏ pr ∈ (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).pairs,
          orderedQuarticPairValue ε β d (d.assembleVertexOrder orders shuffle)
            τ pr.1 pr.2 := by
    rw [← Finset.attach_eq_univ]
    simpa using
      Finset.prod_attach
        (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).pairs
        (fun pr => orderedQuarticPairValue ε β d
          (d.assembleVertexOrder orders shuffle) τ pr.1 pr.2)
  have hlocal (B : d.componentPartition.parts) :
      (∏ pr : d.LocalOrderedPair orders B,
        orderedQuarticPairValue ε β (d.restrictComponent B.2) (orders B)
          (d.componentTimeAssignment shuffle τ B) pr.1.1 pr.1.2) =
        ∏ pr ∈ ((d.restrictComponent B.2).pairingInOrder (orders B)).pairs,
          orderedQuarticPairValue ε β (d.restrictComponent B.2) (orders B)
            (d.componentTimeAssignment shuffle τ B) pr.1 pr.2 := by
    rw [← Finset.attach_eq_univ]
    simpa using
      Finset.prod_attach
        ((d.restrictComponent B.2).pairingInOrder (orders B)).pairs
        (fun pr => orderedQuarticPairValue ε β (d.restrictComponent B.2)
          (orders B) (d.componentTimeAssignment shuffle τ B) pr.1 pr.2)
  calc
    (∏ pr ∈ (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).pairs,
        orderedQuarticPairValue ε β d (d.assembleVertexOrder orders shuffle) τ pr.1 pr.2) =
        (∏ pr : d.GlobalOrderedPair orders shuffle,
          orderedQuarticPairValue ε β d (d.assembleVertexOrder orders shuffle)
            τ pr.1.1 pr.1.2) := hglobal.symm
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
      exact hlocal B

end Fermionic

end SecondQuantization
