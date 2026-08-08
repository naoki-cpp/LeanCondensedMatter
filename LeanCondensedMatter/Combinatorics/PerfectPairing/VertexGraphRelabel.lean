import LeanCondensedMatter.Combinatorics.PerfectPairing.Relabel
import LeanCondensedMatter.Combinatorics.PerfectPairing.VertexGraph

set_option linter.style.header false

/-!
# Vertex graphs under pairing relabeling

Relabeling a perfect pairing along an ambient position permutation transports its induced vertex
graph along any compatible vertex equivalence. This is the graph-level statement needed when a
finite diagram is reindexed from an arbitrary vertex set to explicit ordered slots.
-/

namespace Combinatorics

namespace Pairing

variable {n : ℕ} {Vertex₁ Vertex₂ : Type*}

/-- Adjacency is preserved by a pairing relabel when the leg-to-vertex maps commute with the ambient
position permutation. -/
theorem vertexGraph_relabel_adj_iff
    (P : Pairing n) (e : Equiv.Perm (Fin (2 * n)))
    (vertexEquiv : Vertex₂ ≃ Vertex₁)
    (vertexOfLeg₁ : Fin (2 * n) → Vertex₁)
    (vertexOfLeg₂ : Fin (2 * n) → Vertex₂)
    (hvertex : ∀ leg, vertexOfLeg₁ (e leg) = vertexEquiv (vertexOfLeg₂ leg))
    (v w : Vertex₂) :
    (P.relabel e).vertexGraph vertexOfLeg₂ |>.Adj v w ↔
      P.vertexGraph vertexOfLeg₁ |>.Adj (vertexEquiv v) (vertexEquiv w) := by
  constructor
  · rintro ⟨hvw, leg, hv, hw⟩
    refine ⟨fun h => hvw (vertexEquiv.injective h), e leg, ?_, ?_⟩
    · rw [hvertex, hv]
    · rw [Pairing.relabel_partner] at hw
      have hpartner := hvertex (e.symm (P.partner (e leg)))
      simp only [Equiv.apply_symm_apply] at hpartner
      rw [hpartner, hw]
  · rintro ⟨hvw, leg, hv, hw⟩
    let newLeg := e.symm leg
    refine ⟨fun h => hvw (congrArg vertexEquiv h), newLeg, ?_, ?_⟩
    · apply vertexEquiv.injective
      simpa [newLeg, hvertex] using hv
    · apply vertexEquiv.injective
      have hpartner := hvertex (e.symm (P.partner leg))
      simp only [Equiv.apply_symm_apply] at hpartner
      simpa [newLeg, Pairing.relabel_partner, hpartner] using hw

/-- Reachability is preserved by a compatible pairing relabel. -/
theorem vertexGraph_relabel_reachable_iff
    (P : Pairing n) (e : Equiv.Perm (Fin (2 * n)))
    (vertexEquiv : Vertex₂ ≃ Vertex₁)
    (vertexOfLeg₁ : Fin (2 * n) → Vertex₁)
    (vertexOfLeg₂ : Fin (2 * n) → Vertex₂)
    (hvertex : ∀ leg, vertexOfLeg₁ (e leg) = vertexEquiv (vertexOfLeg₂ leg))
    (v w : Vertex₂) :
    (P.relabel e).vertexGraph vertexOfLeg₂ |>.Reachable v w ↔
      P.vertexGraph vertexOfLeg₁ |>.Reachable (vertexEquiv v) (vertexEquiv w) := by
  rw [SimpleGraph.reachable_iff_reflTransGen, SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail hxy hyz ih =>
        exact Relation.ReflTransGen.tail ih
          ((P.vertexGraph_relabel_adj_iff e vertexEquiv vertexOfLeg₁ vertexOfLeg₂
            hvertex _ _).1 hyz)
  · intro h
    have backward : ∀ {x y : Vertex₁},
        Relation.ReflTransGen (P.vertexGraph vertexOfLeg₁).Adj x y →
          Relation.ReflTransGen ((P.relabel e).vertexGraph vertexOfLeg₂).Adj
            (vertexEquiv.symm x) (vertexEquiv.symm y) := by
      intro x y hxy
      induction hxy with
      | refl => exact Relation.ReflTransGen.refl
      | tail hxy hyz ih =>
          apply Relation.ReflTransGen.tail ih
          apply (P.vertexGraph_relabel_adj_iff e vertexEquiv vertexOfLeg₁ vertexOfLeg₂
            hvertex (vertexEquiv.symm _) (vertexEquiv.symm _)).2
          simpa using hyz
    simpa using backward h

end Pairing

end Combinatorics
