import Mathlib

set_option linter.style.header false

/-!
# Quartic leg indexing

Statistics-independent indexing of four-legged vertices, both by abstract vertex slots and by a
fixed enumeration of a finite vertex set.
-/

namespace SecondQuantization
namespace Common

variable {N : ℕ}

/-- A flattened position is a vertex slot together with a local leg. -/
noncomputable def orderedQuarticLegEquiv (n : ℕ) : Fin (2 * (2 * n)) ≃ Fin n × Fin 4 :=
  (finCongr (by ring)).trans (finProdFinEquiv (m := n) (n := 4)).symm

/-- The vertex slot containing an ordered flattened quartic leg. -/
noncomputable def flatVertexIndex (n : ℕ) (p : Fin (2 * (2 * n))) : Fin n :=
  (orderedQuarticLegEquiv n p).1

/-- The local leg index of an ordered flattened quartic leg. -/
noncomputable def flatLocalLeg (n : ℕ) (p : Fin (2 * (2 * n))) : Fin 4 :=
  (orderedQuarticLegEquiv n p).2

/-- The ordered quartic-leg equivalence sends the block coordinate `i * 4 + j` to `(i, j)`. -/
theorem orderedQuarticLegEquiv_cast_mul_add {n : ℕ} (i : Fin n) (j : Fin 4)
    (h : 2 * (2 * n) = n * 4) :
    orderedQuarticLegEquiv n (Fin.cast h.symm ⟨(i : ℕ) * 4 + (j : ℕ), by omega⟩) = (i, j) := by
  simp only [orderedQuarticLegEquiv, Equiv.trans_apply, finCongr_apply, Fin.cast_cast,
    Fin.cast_eq_self]
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  simp only [finProdFinEquiv, Equiv.coe_fn_mk]
  ring

/-- Every ordered flattened quartic leg is the block coordinate of its vertex and local-leg
projections. -/
theorem eq_cast_mul_add_orderedQuarticLegEquiv {n : ℕ} (p : Fin (2 * (2 * n)))
    (h : 2 * (2 * n) = n * 4) :
    p = Fin.cast h.symm ⟨(orderedQuarticLegEquiv n p).1 * 4 + (orderedQuarticLegEquiv n p).2, by
      have := (orderedQuarticLegEquiv n p).2.isLt
      omega⟩ := by
  have heq := orderedQuarticLegEquiv_cast_mul_add (orderedQuarticLegEquiv n p).1
    (orderedQuarticLegEquiv n p).2 h
  rw [Prod.mk.eta] at heq
  exact ((orderedQuarticLegEquiv n).injective heq).symm

/-- Equivalence between ordered vertex slots and vertices of a finite vertex set. -/
noncomputable def quarticVertexEquiv (S : Finset (Fin N)) : Fin S.card ≃ (↥S) :=
  (finCongr (Fintype.card_coe S)).symm.trans (Fintype.equivFin (↥S)).symm

/-- A flattened position is a vertex of `S` together with a local leg. -/
noncomputable def quarticLegEquiv (S : Finset (Fin N)) :
    Fin (2 * (2 * S.card)) ≃ (↥S) × Fin 4 :=
  (orderedQuarticLegEquiv S.card).trans ((quarticVertexEquiv S).prodCongr (Equiv.refl (Fin 4)))

/-- Vertex incident to a flattened quartic leg. -/
noncomputable def vertexOfLeg {S : Finset (Fin N)} (leg : Fin (2 * (2 * S.card))) : ↥S :=
  (quarticLegEquiv S leg).1

/-- Local leg index of a flattened quartic leg. -/
noncomputable def localLegOfLeg {S : Finset (Fin N)} (leg : Fin (2 * (2 * S.card))) : Fin 4 :=
  (quarticLegEquiv S leg).2

/-- Flatten a vertex and local leg index into the global leg index. -/
noncomputable def legOfVertexLocal {S : Finset (Fin N)} (v : ↥S) (l : Fin 4) :
    Fin (2 * (2 * S.card)) :=
  (quarticLegEquiv S).symm (v, l)

@[simp] theorem vertexOfLeg_legOfVertexLocal {S : Finset (Fin N)} (v : ↥S) (l : Fin 4) :
    vertexOfLeg (legOfVertexLocal v l) = v := by simp [vertexOfLeg, legOfVertexLocal]

@[simp] theorem localLegOfLeg_legOfVertexLocal {S : Finset (Fin N)} (v : ↥S) (l : Fin 4) :
    localLegOfLeg (legOfVertexLocal v l) = l := by simp [localLegOfLeg, legOfVertexLocal]

end Common

end SecondQuantization