import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentPairProduct
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.PairingWeight

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

namespace Common.BlochDeDominicis

/-- A strictly monotone embedding preserves and reflects the crossing relation. -/
theorem crosses_map_iff {n m : ℕ} (f : Fin (2 * n) → Fin (2 * m)) (hf : StrictMono f)
    (a b c e : Fin (2 * n)) :
    Crosses (f a, f b) (f c, f e) ↔ Crosses (a, b) (c, e) := by
  constructor
  · rintro ⟨hac, hcb, hbe⟩
    refine ⟨?_, ?_, ?_⟩
    · apply lt_of_not_ge
      intro hca
      exact (not_lt_of_ge (hf.monotone hca)) hac
    · apply lt_of_not_ge
      intro hbc
      exact (not_lt_of_ge (hf.monotone hbc)) hcb
    · apply lt_of_not_ge
      intro heb
      exact (not_lt_of_ge (hf.monotone heb)) hbe
  · rintro ⟨hac, hcb, hbe⟩
    exact ⟨hf hac, hf hcb, hf hbe⟩

end Common.BlochDeDominicis

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

end SecondQuantization
