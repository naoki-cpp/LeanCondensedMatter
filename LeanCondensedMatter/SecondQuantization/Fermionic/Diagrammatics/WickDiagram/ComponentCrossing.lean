import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentPairProduct

set_option linter.style.header false

/-!
# Component-local crossing compatibility

The ordered-leg embedding of a connected component is strictly monotone, so it preserves and
reflects the geometric crossing relation between component-local normalized pairs.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} {N : ℕ}

/-- Two pairs belonging to the same component cross in the assembled global order exactly when their
component-local representatives cross. -/
theorem QuarticWickDiagram.crosses_componentOrderedLeg_iff {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts)
    (a b c e : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    Combinatorics.Crosses
        (d.componentOrderedLeg shuffle B a, d.componentOrderedLeg shuffle B b)
        (d.componentOrderedLeg shuffle B c, d.componentOrderedLeg shuffle B e) ↔
      Combinatorics.Crosses (a, b) (c, e) :=
  Combinatorics.crosses_map_iff
    (d.componentOrderedLegOrderEmbedding shuffle B)
    (d.componentOrderedLegOrderEmbedding shuffle B).strictMono a b c e

/-- Crossing compatibility stated directly through the component-pair equivalence. -/
@[simp]
theorem QuarticWickDiagram.crosses_componentPairEquiv_iff {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (orders : d.ComponentVertexOrders)
    (shuffle : d.ComponentShuffle) (B : d.componentPartition.parts)
    (p q : d.LocalOrderedPair orders B) :
    Combinatorics.Crosses
        (d.componentPairEquiv orders shuffle ⟨B, p⟩).1
        (d.componentPairEquiv orders shuffle ⟨B, q⟩).1 ↔
      Combinatorics.Crosses p.1 q.1 := by
  rw [d.componentPairEquiv_apply, d.componentPairEquiv_apply]
  exact d.crosses_componentOrderedLeg_iff shuffle B p.1.1 p.1.2 q.1.1 q.1.2

end Fermionic
end SecondQuantization
