import LeanCondensedMatter.Combinatorics.PerfectPairing.Split
import Mathlib.Combinatorics.SimpleGraph.Sum
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


/-- Splitting the legs of a pairing induces a disjoint sum of vertex graphs when the
incidence maps identify the two vertex sectors with disjoint summands. -/
noncomputable def Pairing.vertexGraphOfSplitIso
    {a b n : ℕ} {V W U : Type*}
    (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b)
    (leftVertex : Fin (2 * a) → V) (rightVertex : Fin (2 * b) → W)
    (vertexEquiv : V ⊕ W ≃ U) (vertexOfLeg : Fin (2 * n) → U)
    (hleft : ∀ i, vertexOfLeg (e (Sum.inl i)) =
      vertexEquiv (Sum.inl (leftVertex i)))
    (hright : ∀ i, vertexOfLeg (e (Sum.inr i)) =
      vertexEquiv (Sum.inr (rightVertex i))) :
    (P.vertexGraph leftVertex ⊕g Q.vertexGraph rightVertex) ≃g
      (Pairing.ofSplit e P Q).vertexGraph vertexOfLeg where
  toEquiv := vertexEquiv
  map_rel_iff' := by
    intro x y
    constructor
    · rintro ⟨hne, leg, hx, hy⟩
      obtain ⟨z, rfl⟩ := e.surjective leg
      cases z with
      | inl i =>
          rw [hleft, Pairing.ofSplit_partner_inl, hleft] at hx hy
          have hx' : x = Sum.inl (leftVertex i) :=
            (vertexEquiv.injective hx).symm
          have hy' : y = Sum.inl (leftVertex (P.partner i)) :=
            (vertexEquiv.injective hy).symm
          subst x
          subst y
          change (P.vertexGraph leftVertex).Adj _ _
          refine ⟨?_, i, rfl, rfl⟩
          intro hxy
          exact hne (congrArg vertexEquiv (congrArg Sum.inl hxy))
      | inr i =>
          rw [hright, Pairing.ofSplit_partner_inr, hright] at hx hy
          have hx' : x = Sum.inr (rightVertex i) :=
            (vertexEquiv.injective hx).symm
          have hy' : y = Sum.inr (rightVertex (Q.partner i)) :=
            (vertexEquiv.injective hy).symm
          subst x
          subst y
          change (Q.vertexGraph rightVertex).Adj _ _
          refine ⟨?_, i, rfl, rfl⟩
          intro hxy
          exact hne (congrArg vertexEquiv (congrArg Sum.inr hxy))
    · cases x with
      | inl x =>
          cases y with
          | inl y =>
              intro hadj
              obtain ⟨hne, i, hi, hj⟩ := hadj
              refine ⟨?_, e (Sum.inl i), ?_, ?_⟩
              · intro heq
                exact hne (Sum.inl.inj (vertexEquiv.injective heq))
              · rw [hleft, hi]
              · rw [Pairing.ofSplit_partner_inl, hleft, hj]
          | inr y =>
              intro hadj
              cases hadj
      | inr x =>
          cases y with
          | inl y =>
              intro hadj
              cases hadj
          | inr y =>
              intro hadj
              obtain ⟨hne, i, hi, hj⟩ := hadj
              refine ⟨?_, e (Sum.inr i), ?_, ?_⟩
              · intro heq
                exact hne (Sum.inr.inj (vertexEquiv.injective heq))
              · rw [hright, hi]
              · rw [Pairing.ofSplit_partner_inr, hright, hj]

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


/-- Paired legs determine the same connected-component block in the induced vertex graph. -/
theorem Pairing.vertexGraph_componentBlock_partner {n : ℕ} {Vertex : Type*}
    [DecidableEq Vertex] [Fintype Vertex]
    (pairing : Pairing n) (vertexOfLeg : Fin (2 * n) → Vertex) (leg : Fin (2 * n)) :
    (pairing.vertexGraph vertexOfLeg).componentBlock (vertexOfLeg leg) =
      (pairing.vertexGraph vertexOfLeg).componentBlock
        (vertexOfLeg (pairing.partner leg)) :=
  (pairing.vertexGraph vertexOfLeg).componentBlock_eq_of_reachable
    (pairing.vertexGraph_reachable_partner vertexOfLeg leg).symm

/-- Paired legs determine the same ambient component block when the induced graph is on a finite
subtype. -/
theorem Pairing.vertexGraph_componentBlockOn_partner
    {n : ℕ} {α : Type*} [DecidableEq α] {s : Finset α}
    (pairing : Pairing n) (vertexOfLeg : Fin (2 * n) → ↥s) (leg : Fin (2 * n)) :
    (pairing.vertexGraph vertexOfLeg).componentBlockOn (vertexOfLeg leg) =
      (pairing.vertexGraph vertexOfLeg).componentBlockOn
        (vertexOfLeg (pairing.partner leg)) :=
  (pairing.vertexGraph vertexOfLeg).componentBlockOn_eq_of_reachable
    (pairing.vertexGraph_reachable_partner vertexOfLeg leg).symm

end Combinatorics
