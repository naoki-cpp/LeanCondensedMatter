import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentPairProduct

set_option linter.style.header false

/-!
# Component-local crossing compatibility

The ordered-leg embedding of a connected component is strictly monotone. Consequently it preserves
and reflects the geometric crossing relation between component-local normalized pairs. This isolates
the within-component part of pairing-sign factorization from the remaining parity argument for
crossings between distinct components.
-/

namespace SecondQuantization

variable {Mode : Type*} {N : ℕ}

/-- Two pairs belonging to the same component cross in the assembled global order exactly when their
component-local representatives cross. -/
theorem QuarticWickDiagram.crosses_componentOrderedLeg_iff {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts)
    (a b c e : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    Common.BlochDeDominicis.Crosses
        (d.componentOrderedLeg shuffle B a, d.componentOrderedLeg shuffle B b)
        (d.componentOrderedLeg shuffle B c, d.componentOrderedLeg shuffle B e) ↔
      Common.BlochDeDominicis.Crosses (a, b) (c, e) :=
  Common.BlochDeDominicis.crosses_map_iff
    (d.componentOrderedLegOrderEmbedding shuffle B)
    (d.componentOrderedLegOrderEmbedding shuffle B).strictMono a b c e

/-- Crossing compatibility stated directly through the component-pair equivalence. -/
@[simp]
theorem QuarticWickDiagram.crosses_componentPairEquiv_iff {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (orders : d.ComponentVertexOrders)
    (shuffle : d.ComponentShuffle) (B : d.componentPartition.parts)
    (p q : d.LocalOrderedPair orders B) :
    Common.BlochDeDominicis.Crosses
        (d.componentPairEquiv orders shuffle ⟨B, p⟩).1
        (d.componentPairEquiv orders shuffle ⟨B, q⟩).1 ↔
      Common.BlochDeDominicis.Crosses p.1 q.1 := by
  rw [d.componentPairEquiv_apply, d.componentPairEquiv_apply]
  exact d.crosses_componentOrderedLeg_iff shuffle B p.1.1 p.1.2 q.1.1 q.1.2

/-- Ordered pair-of-pairs that cross inside one restricted component. -/
abbrev QuarticWickDiagram.LocalCrossingPair {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (orders : d.ComponentVertexOrders)
    (B : d.componentPartition.parts) :=
  ((d.restrictComponent B.2).pairingInOrder (orders B)).CrossingPair

/-- Ordered pair-of-pairs that cross in the assembled global pairing. -/
abbrev QuarticWickDiagram.GlobalCrossingPair {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (orders : d.ComponentVertexOrders)
    (shuffle : d.ComponentShuffle) :=
  (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).CrossingPair

/-- Embed a crossing pair-of-pairs from one component into the assembled global pairing. -/
noncomputable def QuarticWickDiagram.componentCrossingPairToGlobal
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts) :
    d.LocalCrossingPair orders B → d.GlobalCrossingPair orders shuffle :=
  fun x =>
    ⟨(d.componentPairEquiv orders shuffle ⟨B, x.1.1⟩,
      d.componentPairEquiv orders shuffle ⟨B, x.1.2⟩),
      (d.crosses_componentPairEquiv_iff orders shuffle B x.1.1 x.1.2).2 x.2⟩

/-- The component crossing-pair map is injective. -/
theorem QuarticWickDiagram.componentCrossingPairToGlobal_injective
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts) :
    Function.Injective (d.componentCrossingPairToGlobal orders shuffle B) := by
  intro x y hxy
  apply Subtype.ext
  have hval := congrArg Subtype.val hxy
  apply Prod.ext
  · have hfirst := congrArg Prod.fst hval
    have hsigma := (d.componentPairEquiv orders shuffle).injective hfirst
    exact eq_of_heq (Sigma.mk.inj_iff.mp hsigma).2
  · have hsecond := congrArg Prod.snd hval
    have hsigma := (d.componentPairEquiv orders shuffle).injective hsecond
    exact eq_of_heq (Sigma.mk.inj_iff.mp hsigma).2

/-- Embed all component-local crossing pair-of-pairs into the assembled global pairing. -/
noncomputable def QuarticWickDiagram.componentCrossingPairsToGlobal
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle) :
    (Σ B : d.componentPartition.parts, d.LocalCrossingPair orders B) →
      d.GlobalCrossingPair orders shuffle :=
  fun x => d.componentCrossingPairToGlobal orders shuffle x.1 x.2

/-- Crossing pair-of-pairs coming from different components remain distinct after global assembly. -/
theorem QuarticWickDiagram.componentCrossingPairsToGlobal_injective
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle) :
    Function.Injective (d.componentCrossingPairsToGlobal orders shuffle) := by
  rintro ⟨B, x⟩ ⟨C, y⟩ hxy
  have hval := congrArg Subtype.val hxy
  have hfirst := congrArg Prod.fst hval
  have hsigmaFirst := (d.componentPairEquiv orders shuffle).injective hfirst
  have hBC : B = C := congrArg Sigma.fst hsigmaFirst
  subst C
  have hxyLocal := d.componentCrossingPairToGlobal_injective orders shuffle B hxy
  cases hxyLocal
  rfl

/-- The subset of assembled global crossings whose two pairs belong to one component. -/
noncomputable def QuarticWickDiagram.internalCrossingPairs
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle) :
    Finset (d.GlobalCrossingPair orders shuffle) := by
  classical
  exact Finset.univ.image (d.componentCrossingPairsToGlobal orders shuffle)

/-- The number of assembled within-component crossings is exactly the sum of the local crossing
counts. -/
theorem QuarticWickDiagram.card_internalCrossingPairs_eq_sum_crossingCount
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle) :
    (d.internalCrossingPairs orders shuffle).card =
      ∑ B : d.componentPartition.parts,
        ((d.restrictComponent B.2).pairingInOrder (orders B)).crossingCount := by
  classical
  rw [QuarticWickDiagram.internalCrossingPairs,
    Finset.card_image_of_injective _
      (d.componentCrossingPairsToGlobal_injective orders shuffle)]
  simp only [Finset.card_univ, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro B _
  have hcard :=
    ((d.restrictComponent B.2).pairingInOrder (orders B)).crossingCount_eq_card_crossingPair
  exact hcard.symm

end SecondQuantization
