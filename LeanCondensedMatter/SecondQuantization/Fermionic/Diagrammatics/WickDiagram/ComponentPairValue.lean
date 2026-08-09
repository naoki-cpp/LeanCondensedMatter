import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.ComponentPairing
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.ComponentOrderedSimplex
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.Amplitude

set_option linter.style.header false

/-!
# Component-local fermionic pair values

Statistics-independent component leg embeddings and pairing compatibility live in
`SecondQuantization.Common`.  This file contains the fermionic operator and pair-value compatibility
specialized to those common embeddings, plus the flattened-leg ordering lemma still used by the
legacy crossing-parity stack.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} {N : ℕ}

/-- Flattened quartic legs in distinct vertex-slot blocks are ordered exactly by their slots.
This remains here only for the legacy crossing-parity stack and can disappear with that stack. -/
theorem orderedQuarticLegEquiv_symm_lt_symm_iff_fst_lt_of_ne
    (n : ℕ) (i j : Fin n) (a b : Fin 4) (hij : i ≠ j) :
    (Common.orderedQuarticLegEquiv n).symm (i, a) <
        (Common.orderedQuarticLegEquiv n).symm (j, b) ↔ i < j := by
  have hp := Common.orderedQuarticLegEquiv_reconstruct_val n
    ((Common.orderedQuarticLegEquiv n).symm (i, a))
  have hq := Common.orderedQuarticLegEquiv_reconstruct_val n
    ((Common.orderedQuarticLegEquiv n).symm (j, b))
  have hp' : ((Common.orderedQuarticLegEquiv n).symm (i, a)).val = a.val + 4 * i.val := by
    simpa using hp
  have hq' : ((Common.orderedQuarticLegEquiv n).symm (j, b)).val = b.val + 4 * j.val := by
    simpa using hq
  change ((Common.orderedQuarticLegEquiv n).symm (i, a)).val <
      ((Common.orderedQuarticLegEquiv n).symm (j, b)).val ↔ i.val < j.val
  rw [hp', hq']
  have ha : a.val < 4 := a.isLt
  have hb : b.val < 4 := b.isLt
  have hij' : i.val ≠ j.val := by
    intro h
    exact hij (Fin.ext h)
  omega

section Fermionic

variable [LinearOrder Mode]

/-- A global ordered leg at a component-embedded position equals the corresponding ordered leg of
its restricted component diagram. -/
theorem orderedQuarticLegOperator_componentOrderedLeg
    (ε : Mode → ℝ) {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
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

variable [Fintype Mode]

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

end Fermionic

end Fermionic
end SecondQuantization
