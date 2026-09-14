import Mathlib.Logic.Equiv.Fin.Basic

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

/-- The row-major coordinate `i * k + j` lies in the `n * k` flattened block range. -/
theorem blockCoordinate_lt {n k : ℕ} (i : Fin n) (j : Fin k) :
    (i : ℕ) * k + (j : ℕ) < n * k := by
  calc
    (i : ℕ) * k + (j : ℕ) < (i : ℕ) * k + k := Nat.add_lt_add_left j.isLt _
    _ = ((i : ℕ) + 1) * k := by rw [Nat.succ_mul]
    _ ≤ n * k := Nat.mul_le_mul_right k i.isLt

/-- The block equivalence sends the flat coordinate `i * k + j` to `(i, j)`. -/
@[simp]
theorem blockEquiv_cast_mul_add {total n k : ℕ} (h : total = n * k)
    (i : Fin n) (j : Fin k) :
    blockEquiv h
        (Fin.cast h.symm ⟨(i : ℕ) * k + (j : ℕ), blockCoordinate_lt i j⟩) = (i, j) := by
  simp only [blockEquiv, Equiv.trans_apply, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self]
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  simp only [finProdFinEquiv, Equiv.coe_fn_mk]
  ac_rfl

/-- Every flat finite index is the block coordinate obtained from its block/local projections. -/
theorem eq_cast_mul_add_blockEquiv {total n k : ℕ} (h : total = n * k) (p : Fin total) :
    p = Fin.cast h.symm
      ⟨(blockEquiv h p).1 * k + (blockEquiv h p).2,
        blockCoordinate_lt (blockEquiv h p).1 (blockEquiv h p).2⟩ := by
  have heq := blockEquiv_cast_mul_add h (blockEquiv h p).1 (blockEquiv h p).2
  rw [Prod.mk.eta] at heq
  exact ((blockEquiv h).injective heq).symm

private theorem blockEquiv_reconstruct_val {total n k : ℕ} (h : total = n * k)
    (p : Fin total) :
    p.val = (blockEquiv h p).2.val + k * (blockEquiv h p).1.val := by
  have hp := congrArg Fin.val (eq_cast_mul_add_blockEquiv h p)
  simpa [Nat.mul_comm, Nat.add_comm] using hp

private theorem local_add_block_mul_lt_of_block_lt {n k : ℕ}
    (i j : Fin n) (a b : Fin k) (hij : i < j) :
    (a : ℕ) + k * (i : ℕ) < (b : ℕ) + k * (j : ℕ) := by
  calc
    (a : ℕ) + k * (i : ℕ) < k + k * (i : ℕ) := Nat.add_lt_add_right a.isLt _
    _ = ((i : ℕ) + 1) * k := by
      rw [Nat.succ_mul]
      ac_rfl
    _ ≤ (j : ℕ) * k := Nat.mul_le_mul_right k hij
    _ = k * (j : ℕ) := Nat.mul_comm _ _
    _ ≤ (b : ℕ) + k * (j : ℕ) := Nat.le_add_left _ _

/-- Flat order is the lexicographic order on the block index followed by the local index. -/
theorem blockEquiv_lt_iff {total n k : ℕ} (h : total = n * k) (p q : Fin total) :
    p < q ↔
      (blockEquiv h p).1 < (blockEquiv h q).1 ∨
        ((blockEquiv h p).1 = (blockEquiv h q).1 ∧
          (blockEquiv h p).2 < (blockEquiv h q).2) := by
  have hp := blockEquiv_reconstruct_val h p
  have hq := blockEquiv_reconstruct_val h q
  constructor
  · intro hpq
    rcases lt_trichotomy (blockEquiv h p).1 (blockEquiv h q).1 with hlt | heq | hgt
    · exact Or.inl hlt
    · refine Or.inr ⟨heq, ?_⟩
      have hblock : (blockEquiv h p).1.val = (blockEquiv h q).1.val := congrArg Fin.val heq
      have hval : p.val < q.val := hpq
      rw [hp, hq, hblock] at hval
      exact Nat.add_lt_add_iff_right.mp hval
    · have hval : p.val < q.val := hpq
      rw [hp, hq] at hval
      have hrev := local_add_block_mul_lt_of_block_lt
        (blockEquiv h q).1 (blockEquiv h p).1
        (blockEquiv h q).2 (blockEquiv h p).2 hgt
      exact (lt_asymm hval hrev).elim
  · rintro (hlt | ⟨heq, hlocal⟩)
    · have hcoord := local_add_block_mul_lt_of_block_lt
        (blockEquiv h p).1 (blockEquiv h q).1
        (blockEquiv h p).2 (blockEquiv h q).2 hlt
      change p.val < q.val
      rw [hp, hq]
      exact hcoord
    · have hblock : (blockEquiv h p).1.val = (blockEquiv h q).1.val := congrArg Fin.val heq
      change p.val < q.val
      rw [hp, hq, hblock]
      exact Nat.add_lt_add_right hlocal _

/-- Flat coordinates in distinct blocks are ordered exactly by their block indices. -/
theorem blockEquiv_symm_lt_symm_iff_fst_lt_of_ne {total n k : ℕ}
    (h : total = n * k) (i j : Fin n) (a b : Fin k) (hij : i ≠ j) :
    (blockEquiv h).symm (i, a) < (blockEquiv h).symm (j, b) ↔ i < j := by
  have hlex := blockEquiv_lt_iff h
    ((blockEquiv h).symm (i, a)) ((blockEquiv h).symm (j, b))
  simpa [hij] using hlex

/-- Flat coordinates in the same block are ordered exactly by their local indices. -/
theorem blockEquiv_symm_lt_symm_iff_snd_lt_of_fst_eq {total n k : ℕ}
    (hcard : total = n * k) (p q : Fin n × Fin k) (h : p.1 = q.1) :
    (blockEquiv hcard).symm p < (blockEquiv hcard).symm q ↔ p.2 < q.2 := by
  have hlex := blockEquiv_lt_iff hcard ((blockEquiv hcard).symm p) ((blockEquiv hcard).symm q)
  simpa [h] using hlex

end FiniteIndex
end Combinatorics
