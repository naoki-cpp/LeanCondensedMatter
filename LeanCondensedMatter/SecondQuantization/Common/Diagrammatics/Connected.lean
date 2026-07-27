import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Diagram
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option linter.style.header false

/-!
# Connectivity of labelled quartic diagrams

The vertex graph and connectedness predicate depend only on the pairing of four-legged vertices,
not on the vertex-label type or particle statistics.
-/

namespace SecondQuantization
namespace Common

variable {Label : Type*} {N : ℕ}

/-- The graph connecting distinct vertices whose legs are paired. -/
noncomputable def QuarticDiagram.vertexGraph {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) : SimpleGraph (↥S) where
  Adj v w := v ≠ w ∧ ∃ leg : Fin (2 * (2 * S.card)),
    vertexOfLeg leg = v ∧ vertexOfLeg (d.pairing.partner leg) = w
  symm := ⟨by
    rintro v w ⟨hvw, leg, hv, hw⟩
    refine ⟨hvw.symm, d.pairing.partner leg, hw, ?_⟩
    rw [d.pairing.partner_involutive leg, hv]⟩
  loopless := ⟨by
    rintro v ⟨hvv, -⟩
    exact hvv rfl⟩

/-- A quartic diagram is connected when its vertex graph is preconnected and `S` is nonempty. -/
def QuarticDiagram.IsConnected {S : Finset (Fin N)} (d : QuarticDiagram Label N S) : Prop :=
  d.vertexGraph.Preconnected ∧ S.Nonempty

/-- The subtype of connected labelled quartic diagrams on vertex set `S`. -/
def ConnectedQuarticDiagram (Label : Type*) (N : ℕ) (S : Finset (Fin N)) : Type _ :=
  {d : QuarticDiagram Label N S // d.IsConnected}

end Common
end SecondQuantization
