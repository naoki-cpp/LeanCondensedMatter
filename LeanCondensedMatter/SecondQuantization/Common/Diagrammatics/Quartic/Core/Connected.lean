import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Diagram
import LeanCondensedMatter.Combinatorics.PerfectPairing.VertexGraph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.EquivFin

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
    (d : QuarticDiagram Label N S) : SimpleGraph (↥S) :=
  d.pairing.vertexGraph vertexOfLeg

/-- A quartic diagram is connected when its vertex graph is preconnected and `S` is nonempty. -/
def QuarticDiagram.IsConnected {S : Finset (Fin N)} (d : QuarticDiagram Label N S) : Prop :=
  d.vertexGraph.Preconnected ∧ S.Nonempty

/-- The subtype of connected labelled quartic diagrams on vertex set `S`. -/
def ConnectedQuarticDiagram (Label : Type*) (N : ℕ) (S : Finset (Fin N)) : Type _ :=
  {d : QuarticDiagram Label N S // d.IsConnected}

/-- Connected labelled quartic diagrams form a finite type when their labels do. -/
noncomputable instance ConnectedQuarticDiagram.instFintype [Fintype Label]
    {S : Finset (Fin N)} : Fintype (ConnectedQuarticDiagram Label N S) :=
  Fintype.ofFinite {d : QuarticDiagram Label N S // d.IsConnected}

end Common
end SecondQuantization
