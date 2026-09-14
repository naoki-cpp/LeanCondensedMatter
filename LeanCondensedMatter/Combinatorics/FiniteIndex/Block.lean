import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Omega

set_option linter.style.header false

/-!
# Fixed-width finite block indexing

Mathlib supplies `finProdFinEquiv : Fin n × Fin k ≃ Fin (n * k)`. This module packages its
inverse together with an arbitrary equality for the total cardinality and records the coordinate and
order facts needed when a flat finite index is viewed as a block index plus a local index.
-/

namespace Combinatorics
namespace FiniteIndex

/-- Identify a flat finite index with a block index and a fixed-width local index. -/
def blockEquiv {total n k : ℕ} (h : total = n * k) : Fin total ≃ Fin n × Fin k :=
  (finCongr h).trans (finProdFinEquiv (m := n) (n := k)).symm

/-- The block equivalence sends the flat coordinate `i * k + j` to `(i, j)`. -/
@[simp]
theorem blockEquiv_cast_mul_add {total n k : ℕ} (h : total = n * k)
    (i : Fin n) (j : Fin k) :
    blockEquiv h (Fin.cast h.symm ⟨(i : ℕ) * k + (j : ℕ), by omega⟩) = (i, j) := by
  simp only [blockEquiv, Equiv.trans_apply, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self]
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  simp only [finProdFinEquiv, Equiv.coe_fn_mk]
  omega

/-- Every flat finite index is the block coordinate obtained from its block/local projections. -/
theorem eq_cast_mul_add_blockEquiv {total n k : ℕ} (h : total = n * k) (p : Fin total) :
    p = Fin.cast h.symm
      ⟨(blockEquiv h p).1 * k + (blockEquiv h p).2, by
        have := (blockEquiv h p).2.isLt
        omega⟩ := by
  have heq := blockEquiv_cast_mul_add h (blockEquiv h p).1 (blockEquiv h p).2
  rw [Prod.mk.eta] at heq
  exact ((blockEquiv h).injective heq).symm

/-- Flat coordinates in distinct blocks are ordered exactly by their block indices. -/
theorem blockEquiv_symm_lt_symm_iff_fst_lt_of_ne {total n k : ℕ}
    (h : total = n * k) (i j : Fin n) (a b : Fin k) (hij : i ≠ j) :
    (blockEquiv h).symm (i, a) < (blockEquiv h).symm (j, b) ↔ i < j := by
  have hp' : ((blockEquiv h).symm (i, a)).val = a.val + k * i.val := by
    simp [blockEquiv, finProdFinEquiv]
  have hq' : ((blockEquiv h).symm (j, b)).val = b.val + k * j.val := by
    simp [blockEquiv, finProdFinEquiv]
  change ((blockEquiv h).symm (i, a)).val <
      ((blockEquiv h).symm (j, b)).val ↔ i.val < j.val
  rw [hp', hq']
  have ha : a.val < k := a.isLt
  have hb : b.val < k := b.isLt
  have hij' : i.val ≠ j.val := by
    intro hijVal
    exact hij (Fin.ext hijVal)
  omega

/-- Flat coordinates in the same block are ordered exactly by their local indices. -/
theorem blockEquiv_symm_lt_symm_iff_snd_lt_of_fst_eq {total n k : ℕ}
    (hcard : total = n * k) (p q : Fin n × Fin k) (h : p.1 = q.1) :
    (blockEquiv hcard).symm p < (blockEquiv hcard).symm q ↔ p.2 < q.2 := by
  rcases p with ⟨i, a⟩
  rcases q with ⟨j, b⟩
  change i = j at h
  subst j
  have hp' : ((blockEquiv hcard).symm (i, a)).val = a.val + k * i.val := by
    simp [blockEquiv, finProdFinEquiv]
  have hq' : ((blockEquiv hcard).symm (i, b)).val = b.val + k * i.val := by
    simp [blockEquiv, finProdFinEquiv]
  change ((blockEquiv hcard).symm (i, a)).val <
      ((blockEquiv hcard).symm (i, b)).val ↔ a.val < b.val
  rw [hp', hq']
  omega

end FiniteIndex
end Combinatorics
