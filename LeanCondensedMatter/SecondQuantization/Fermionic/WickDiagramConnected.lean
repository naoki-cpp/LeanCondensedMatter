import LeanCondensedMatter.SecondQuantization.Fermionic.WickDiagram
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option linter.style.header false

/-!
# Quartic Wick diagram connectivity

`QuarticWickDiagram.vertexGraph` is the simple graph on the diagram's vertex set in which two
distinct vertices are adjacent when a leg of one is paired with a leg of the other. Pairings between
legs of the same vertex do not produce graph edges.

A diagram is connected when its vertex graph is preconnected and the vertex set is nonempty. This
formulation makes the empty-set convention explicit without requiring a `Nonempty ↥S` instance.
`ConnectedQuarticWickDiagram` is the corresponding subtype.
-/

namespace SecondQuantization

variable {Mode : Type*} {N : ℕ}

/-- The graph connecting distinct vertices whose legs are paired. -/
noncomputable def QuarticWickDiagram.vertexGraph {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) : SimpleGraph (↥S) where
  Adj v w := v ≠ w ∧ ∃ leg : Fin (2 * (2 * S.card)),
    vertexOfLeg leg = v ∧ vertexOfLeg (d.pairing.partner leg) = w
  symm := ⟨by
    rintro v w ⟨hvw, leg, hv, hw⟩
    refine ⟨hvw.symm, d.pairing.partner leg, hw, ?_⟩
    rw [d.pairing.partner_involutive leg, hv]⟩
  loopless := ⟨by
    rintro v ⟨hvv, -⟩
    exact hvv rfl⟩

/-- A quartic Wick diagram is connected when its vertex graph is preconnected and `S` is nonempty. -/
def QuarticWickDiagram.IsConnected {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) : Prop :=
  d.vertexGraph.Preconnected ∧ S.Nonempty

/-- The subtype of connected quartic Wick diagrams on vertex set `S`. -/
def ConnectedQuarticWickDiagram (Mode : Type*) (N : ℕ) (S : Finset (Fin N)) : Type _ :=
  {d : QuarticWickDiagram Mode N S // d.IsConnected}

end SecondQuantization
