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
    (d.componentOrderedLeg shuffle B) (d.componentOrderedLeg_strictMono shuffle B) a b c e

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
    ⟨((d.componentOrderedLeg shuffle B x.1.1.1,
        d.componentOrderedLeg shuffle B x.1.1.2),
      (d.componentOrderedLeg shuffle B x.1.2.1,
        d.componentOrderedLeg shuffle B x.1.2.2)),
      (d.mem_pairingInOrder_pairs_componentOrderedLeg_iff
        orders shuffle B x.1.1.1 x.1.1.2).2 x.2.1,
      (d.mem_pairingInOrder_pairs_componentOrderedLeg_iff
        orders shuffle B x.1.2.1 x.1.2.2).2 x.2.2.1,
      (d.crosses_componentOrderedLeg_iff shuffle B
        x.1.1.1 x.1.1.2 x.1.2.1 x.1.2.2).2 x.2.2.2⟩

/-- The component crossing-pair map is injective. -/
theorem QuarticWickDiagram.componentCrossingPairToGlobal_injective
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts) :
    Function.Injective (d.componentCrossingPairToGlobal orders shuffle B) := by
  intro x y hxy
  apply Subtype.ext
  have hval := congrArg Subtype.val hxy
  change
    ((d.componentOrderedLeg shuffle B x.1.1.1,
        d.componentOrderedLeg shuffle B x.1.1.2),
      (d.componentOrderedLeg shuffle B x.1.2.1,
        d.componentOrderedLeg shuffle B x.1.2.2)) =
    ((d.componentOrderedLeg shuffle B y.1.1.1,
        d.componentOrderedLeg shuffle B y.1.1.2),
      (d.componentOrderedLeg shuffle B y.1.2.1,
        d.componentOrderedLeg shuffle B y.1.2.2)) at hval
  apply Prod.ext
  · apply Prod.ext
    · exact d.componentOrderedLeg_injective shuffle B (congrArg (fun z => z.1.1) hval)
    · exact d.componentOrderedLeg_injective shuffle B (congrArg (fun z => z.1.2) hval)
  · apply Prod.ext
    · exact d.componentOrderedLeg_injective shuffle B (congrArg (fun z => z.2.1) hval)
    · exact d.componentOrderedLeg_injective shuffle B (congrArg (fun z => z.2.2) hval)

end SecondQuantization
