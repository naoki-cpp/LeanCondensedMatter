import Mathlib

set_option linter.style.header false

/-!
# Quartic leg indexing

Statistics-independent bookkeeping for four-legged vertices. A flattened position among `n`
vertices is identified with a vertex slot and a local leg in `Fin 4`. For a finite vertex set `S`,
the same construction uses a fixed enumeration of `S` to identify flattened positions with
`↥S × Fin 4`.
-/

namespace SecondQuantization

variable {N : ℕ}

/-- The flattened-leg/local-leg equivalence for an abstract vertex count `n`. -/
noncomputable def orderedQuarticLegEquiv (n : ℕ) : Fin (2 * (2 * n)) ≃ Fin n × Fin 4 :=
  (finCongr (by ring)).trans (finProdFinEquiv (m := n) (n := 4)).symm

/-- The fixed vertex enumeration used by `quarticLegEquiv`. -/
noncomputable def quarticVertexEquiv (S : Finset (Fin N)) : Fin S.card ≃ (↥S) :=
  (finCongr (Fintype.card_coe S)).symm.trans (Fintype.equivFin (↥S)).symm

/-- A flattened leg position is equivalent to a vertex of `S` and a local leg. -/
noncomputable def quarticLegEquiv (S : Finset (Fin N)) :
    Fin (2 * (2 * S.card)) ≃ (↥S) × Fin 4 :=
  (orderedQuarticLegEquiv S.card).trans ((quarticVertexEquiv S).prodCongr (Equiv.refl (Fin 4)))

/-- The vertex containing a flattened leg position. -/
noncomputable def vertexOfLeg {S : Finset (Fin N)} (leg : Fin (2 * (2 * S.card))) : ↥S :=
  (quarticLegEquiv S leg).1

/-- The local leg selected by a flattened leg position. -/
noncomputable def localLegOfLeg {S : Finset (Fin N)} (leg : Fin (2 * (2 * S.card))) : Fin 4 :=
  (quarticLegEquiv S leg).2

/-- The flattened leg position corresponding to a vertex and local leg. -/
noncomputable def legOfVertexLocal {S : Finset (Fin N)} (v : ↥S) (l : Fin 4) :
    Fin (2 * (2 * S.card)) :=
  (quarticLegEquiv S).symm (v, l)

@[simp]
theorem vertexOfLeg_legOfVertexLocal {S : Finset (Fin N)} (v : ↥S) (l : Fin 4) :
    vertexOfLeg (legOfVertexLocal v l) = v := by
  simp [vertexOfLeg, legOfVertexLocal]

@[simp]
theorem localLegOfLeg_legOfVertexLocal {S : Finset (Fin N)} (v : ↥S) (l : Fin 4) :
    localLegOfLeg (legOfVertexLocal v l) = l := by
  simp [localLegOfLeg, legOfVertexLocal]

end SecondQuantization
