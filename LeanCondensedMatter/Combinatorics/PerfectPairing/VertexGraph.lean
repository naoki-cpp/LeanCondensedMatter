import LeanCondensedMatter.Combinatorics.PerfectPairing.Core
import LeanCondensedMatter.Combinatorics.SimpleGraphComponentPartition

set_option linter.style.header false

/-!
# Vertex graphs induced by perfect pairings

A perfect pairing of finitely many legs induces a simple graph on any chosen vertex type once every
leg is assigned to its incident vertex. Two distinct vertices are adjacent exactly when some paired
leg has one endpoint at each vertex.

This construction is independent of diagram labels, particle statistics, and second quantization.
-/

namespace Combinatorics

/-- The simple graph induced by a perfect pairing and a map assigning each paired position to its
incident vertex. -/
noncomputable def Pairing.vertexGraph {n : ℕ} {Vertex : Type*} (pairing : Pairing n)
    (vertexOfLeg : Fin (2 * n) → Vertex) : SimpleGraph Vertex where
  Adj v w := v ≠ w ∧ ∃ leg : Fin (2 * n),
    vertexOfLeg leg = v ∧ vertexOfLeg (pairing.partner leg) = w
  symm := ⟨by
    rintro v w ⟨hvw, leg, hv, hw⟩
    refine ⟨hvw.symm, pairing.partner leg, hw, ?_⟩
    rw [pairing.partner_involutive leg, hv]⟩
  loopless := ⟨by
    rintro v ⟨hvv, -⟩
    exact hvv rfl⟩

/-- The two incident vertices of a paired leg lie in the same connected component of the pairing
vertex graph. -/
theorem Pairing.vertexGraph_reachable_partner {n : ℕ} {Vertex : Type*}
    (pairing : Pairing n) (vertexOfLeg : Fin (2 * n) → Vertex) (leg : Fin (2 * n)) :
    (pairing.vertexGraph vertexOfLeg).Reachable
      (vertexOfLeg (pairing.partner leg)) (vertexOfLeg leg) := by
  by_cases h : vertexOfLeg (pairing.partner leg) = vertexOfLeg leg
  · rw [h]
  · exact SimpleGraph.Adj.reachable
      ⟨h, pairing.partner leg, rfl, by rw [pairing.partner_involutive]⟩


/-- Pairing partners determine the same connected-component block in the induced vertex graph. -/
theorem Pairing.vertexGraph_componentBlock_partner {n : ℕ} {Vertex : Type*}
    [Fintype Vertex] [DecidableEq Vertex] (pairing : Pairing n)
    (vertexOfLeg : Fin (2 * n) → Vertex) (leg : Fin (2 * n)) :
    (pairing.vertexGraph vertexOfLeg).componentBlock (vertexOfLeg leg) =
      (pairing.vertexGraph vertexOfLeg).componentBlock (vertexOfLeg (pairing.partner leg)) :=
  (pairing.vertexGraph vertexOfLeg).componentBlock_eq_of_reachable
    (pairing.vertexGraph_reachable_partner vertexOfLeg leg).symm

/-- Pairing partners determine the same ambient component block for a graph on a finite subtype. -/
theorem Pairing.vertexGraph_componentBlockOn_partner {n : ℕ} {Vertex : Type*}
    [DecidableEq Vertex] {S : Finset Vertex} (pairing : Pairing n)
    (vertexOfLeg : Fin (2 * n) → ↥S) (leg : Fin (2 * n)) :
    (pairing.vertexGraph vertexOfLeg).componentBlockOn (vertexOfLeg leg) =
      (pairing.vertexGraph vertexOfLeg).componentBlockOn (vertexOfLeg (pairing.partner leg)) :=
  (pairing.vertexGraph vertexOfLeg).componentBlockOn_eq_of_reachable
    (pairing.vertexGraph_reachable_partner vertexOfLeg leg).symm

end Combinatorics
