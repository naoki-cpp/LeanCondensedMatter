import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentOrder
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentOrderedSimplex
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.Amplitude

set_option linter.style.header false

/-!
# Component-local ordered legs and pair values

A component shuffle embeds every component-local ordered flattened leg into the flattened-leg
enumeration of the assembled global vertex order.  This file proves that the associated fermionic leg
operators and normalized pair values agree exactly with those of the restricted component diagram.
These coordinate lemmas are the first part of the contraction-integrand factorization milestone.
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode] {N : ℕ}

/-- Embed a component-local ordered flattened leg into the assembled global ordered-leg enumeration. -/
noncomputable def QuarticWickDiagram.componentOrderedLeg {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts) :
    Fin (2 * (2 * (B : Finset (Fin N)).card)) → Fin (2 * (2 * S.card)) :=
  fun p => (orderedQuarticLegEquiv S.card).symm
    (shuffle.slotEquiv ⟨B, (orderedQuarticLegEquiv (B : Finset (Fin N)).card p).1⟩,
      (orderedQuarticLegEquiv (B : Finset (Fin N)).card p).2)

@[simp]
theorem QuarticWickDiagram.orderedQuarticLegEquiv_componentOrderedLeg
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (shuffle : d.ComponentShuffle) (B : d.componentPartition.parts)
    (p : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    orderedQuarticLegEquiv S.card (d.componentOrderedLeg shuffle B p) =
      (shuffle.slotEquiv ⟨B, (orderedQuarticLegEquiv (B : Finset (Fin N)).card p).1⟩,
        (orderedQuarticLegEquiv (B : Finset (Fin N)).card p).2) := by
  simp [QuarticWickDiagram.componentOrderedLeg]

/-- The component-local ordered-leg map is injective. -/
theorem QuarticWickDiagram.componentOrderedLeg_injective {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts) :
    Function.Injective (d.componentOrderedLeg shuffle B) := by
  intro a b hab
  have hpair := congrArg (orderedQuarticLegEquiv S.card) hab
  have hslot :
      shuffle.slotEquiv ⟨B, (orderedQuarticLegEquiv (B : Finset (Fin N)).card a).1⟩ =
        shuffle.slotEquiv ⟨B, (orderedQuarticLegEquiv (B : Finset (Fin N)).card b).1⟩ :=
    congrArg Prod.fst hpair
  have hlocal :
      (orderedQuarticLegEquiv (B : Finset (Fin N)).card a).2 =
        (orderedQuarticLegEquiv (B : Finset (Fin N)).card b).2 :=
    congrArg Prod.snd hpair
  have hsigma := shuffle.slotEquiv.injective hslot
  have hvertex :
      (orderedQuarticLegEquiv (B : Finset (Fin N)).card a).1 =
        (orderedQuarticLegEquiv (B : Finset (Fin N)).card b).1 := by
    simpa using hsigma
  apply (orderedQuarticLegEquiv (B : Finset (Fin N)).card).injective
  exact Prod.ext hvertex hlocal

/-- The component-local ordered-leg map as an embedding. -/
noncomputable def QuarticWickDiagram.componentOrderedLegEmbedding {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts) :
    Fin (2 * (2 * (B : Finset (Fin N)).card)) ↪ Fin (2 * (2 * S.card)) :=
  ⟨d.componentOrderedLeg shuffle B, d.componentOrderedLeg_injective shuffle B⟩

/-- The assembled global order sends a component slot to the same underlying labelled vertex as its
component-local order. -/
theorem QuarticWickDiagram.assembleVertexOrder_componentSlot_val
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts) (i : Fin (B : Finset (Fin N)).card) :
    ((d.assembleVertexOrder orders shuffle (shuffle.slotEquiv ⟨B, i⟩) : ↥S) : Fin N) =
      ((orders B i : ↥(B : Finset (Fin N))) : Fin N) := by
  simp [QuarticWickDiagram.assembleVertexOrder, QuarticWickDiagram.componentVertexEquiv,
    Common.QuarticDiagram.assembleVertexOrder, Common.QuarticDiagram.componentVertexEquiv]

/-- Vertex labels agree between the assembled global diagram and a restricted component. -/
theorem QuarticWickDiagram.restrictComponent_vertexLabel_componentOrder
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts) (i : Fin (B : Finset (Fin N)).card) :
    (d.restrictComponent B.2).vertexLabel (orders B i) =
      d.vertexLabel (d.assembleVertexOrder orders shuffle (shuffle.slotEquiv ⟨B, i⟩)) := by
  unfold QuarticWickDiagram.restrictComponent Common.QuarticDiagram.restrictComponent
  apply congrArg d.vertexLabel
  apply Subtype.ext
  simpa using (d.assembleVertexOrder_componentSlot_val orders shuffle B i).symm

/-- A global ordered leg at a component-embedded position equals the corresponding ordered leg of the
restricted component diagram. -/
theorem orderedQuarticLegOperator_componentOrderedLeg (ε : Mode → ℝ)
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (τ : Fin S.card → ℝ) (B : d.componentPartition.parts)
    (p : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    orderedQuarticLegOperator ε d (d.assembleVertexOrder orders shuffle) τ
        (d.componentOrderedLeg shuffle B p) =
      orderedQuarticLegOperator ε (d.restrictComponent B.2) (orders B)
        (d.componentTimeAssignment shuffle τ B) p := by
  unfold orderedQuarticLegOperator quarticLegOperatorForSequence
  simp only [d.orderedQuarticLegEquiv_componentOrderedLeg,
    Common.QuarticDiagram.componentTimeAssignment_apply]
  rw [d.restrictComponent_vertexLabel_componentOrder orders shuffle B]

/-- Pair values agree after embedding both component-local ordered legs into the assembled global
ordered-leg enumeration. -/
theorem orderedQuarticPairValue_componentOrderedLeg (ε : Mode → ℝ) (β : ℝ)
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (τ : Fin S.card → ℝ) (B : d.componentPartition.parts)
    (a b : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    orderedQuarticPairValue ε β d (d.assembleVertexOrder orders shuffle) τ
        (d.componentOrderedLeg shuffle B a) (d.componentOrderedLeg shuffle B b) =
      orderedQuarticPairValue ε β (d.restrictComponent B.2) (orders B)
        (d.componentTimeAssignment shuffle τ B) a b := by
  unfold orderedQuarticPairValue
  rw [orderedQuarticLegOperator_componentOrderedLeg,
    orderedQuarticLegOperator_componentOrderedLeg]

end SecondQuantization
