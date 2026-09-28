import LeanCondensedMatter.Combinatorics.FiniteIndex.Block
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
  Combinatorics.FiniteIndex.blockEquiv (by ring)

/-- Reindex a vertex-indexed family of four local values into the canonical row-major
flattened quartic-leg order. -/
noncomputable def orderedQuarticLegFamily {α : Type*} {n : ℕ}
    (f : Fin n → Fin 4 → α) : Fin (2 * (2 * n)) → α :=
  fun p =>
    let vl := orderedQuarticLegEquiv n p
    f vl.1 vl.2

/-- Evaluating the canonical flattened family at the row-major coordinate `i * 4 + j` recovers
the corresponding vertex-local value. -/
private theorem orderedQuarticLegFamily_cast_mul_add {α : Type*} {n : ℕ}
    (f : Fin n → Fin 4 → α) (i : Fin n) (j : Fin 4)
    (h : 2 * (2 * n) = n * 4) :
    orderedQuarticLegFamily f
        (Fin.cast h.symm ⟨(i : ℕ) * 4 + (j : ℕ), by omega⟩) = f i j := by
  have hcoord :
      orderedQuarticLegEquiv n
          (Fin.cast h.symm ⟨(i : ℕ) * 4 + (j : ℕ), by omega⟩) = (i, j) := by
    simpa [orderedQuarticLegEquiv] using
      (Combinatorics.FiniteIndex.blockEquiv_cast_mul_add h i j)
  rw [orderedQuarticLegFamily, hcoord]

/-- Prepending one vertex-local block prepends its four entries to the canonical flattened quartic
leg list. -/
theorem listOfFn_orderedQuarticLegFamily_cons {α : Type*} {n : ℕ}
    (f0 : Fin 4 → α) (f : Fin n → Fin 4 → α) :
    List.ofFn (orderedQuarticLegFamily (Fin.cons f0 f)) =
      List.ofFn f0 ++ List.ofFn (orderedQuarticLegFamily f) := by
  have hcard : 2 * (2 * (n + 1)) = (n + 1) * 4 := by ring
  have hcard' : 2 * (2 * n) = n * 4 := by ring
  have h2 : 2 * (2 * (n + 1)) = 4 + 2 * (2 * n) := by ring
  rw [List.ofFn_congr h2, ← List.ofFn_fin_append]
  refine congrArg List.ofFn (funext (Fin.addCases (fun j => ?_) fun k => ?_))
  · have e1 : Fin.cast h2.symm (Fin.castAdd (2 * (2 * n)) j) =
        Fin.cast hcard.symm ⟨((0 : Fin (n + 1)) : ℕ) * 4 + (j : ℕ), by omega⟩ := by
      apply Fin.ext
      simp
    rw [Fin.append_left, e1,
      orderedQuarticLegFamily_cast_mul_add (Fin.cons f0 f) 0 j hcard, Fin.cons_zero]
  · have hk : k = Fin.cast hcard'.symm
        ⟨(orderedQuarticLegEquiv n k).1 * 4 +
            (orderedQuarticLegEquiv n k).2, by
          have := (orderedQuarticLegEquiv n k).2.isLt
          omega⟩ :=
      Combinatorics.FiniteIndex.eq_cast_mul_add_blockEquiv hcard' k
    have e2 : Fin.cast h2.symm (Fin.natAdd 4 k) = Fin.cast hcard.symm
        ⟨((orderedQuarticLegEquiv n k).1.succ : ℕ) * 4 +
            ((orderedQuarticLegEquiv n k).2 : ℕ),
          by
            have := (orderedQuarticLegEquiv n k).2.isLt
            omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_succ]
      have hkval : (k : ℕ) =
          (orderedQuarticLegEquiv n k).1 * 4 +
            (orderedQuarticLegEquiv n k).2 := by
        have := congrArg Fin.val hk
        simpa using this
      omega
    rw [Fin.append_right, e2,
      orderedQuarticLegFamily_cast_mul_add (Fin.cons f0 f)
        (orderedQuarticLegEquiv n k).1.succ (orderedQuarticLegEquiv n k).2 hcard]
    have hrest := orderedQuarticLegFamily_cast_mul_add f
      (orderedQuarticLegEquiv n k).1 (orderedQuarticLegEquiv n k).2 hcard'
    rw [← hk] at hrest
    exact hrest.symm

/-- The product of the canonical row-major flattened quartic-leg family is the ordered product
of the four-leg product at each vertex. -/
theorem prod_orderedQuarticLegFamily_eq_vertexProducts {α : Type*} [Monoid α] :
    ∀ {n : ℕ} (f : Fin n → Fin 4 → α),
      (List.ofFn (orderedQuarticLegFamily f)).prod =
        (List.ofFn (fun i => (List.ofFn (f i)).prod)).prod := by
  intro n
  induction n with
  | zero =>
      intro f
      simp
  | succ n ih =>
      intro f
      rw [← Fin.cons_self_tail f, listOfFn_orderedQuarticLegFamily_cons, List.prod_append, ih]
      simp only [List.ofFn_succ, List.prod_cons, Fin.cons_zero, Fin.cons_succ]

/-- The vertex slot containing an ordered flattened quartic leg. -/
noncomputable def flatVertexIndex (n : ℕ) (p : Fin (2 * (2 * n))) : Fin n :=
  (orderedQuarticLegEquiv n p).1

/-- The local leg index of an ordered flattened quartic leg. -/
noncomputable def flatLocalLeg (n : ℕ) (p : Fin (2 * (2 * n))) : Fin 4 :=
  (orderedQuarticLegEquiv n p).2

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
