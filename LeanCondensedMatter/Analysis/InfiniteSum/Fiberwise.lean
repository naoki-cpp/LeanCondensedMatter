import Mathlib.Analysis.Normed.Ring.InfiniteSum

set_option linter.style.header false

/-!
# Fiberwise infinite sums

Generic Fubini-style packaging for summable families indexed by a product. This module contains no
operator-theory or condensed-matter content.
-/

/-- **Row-first and column-first iterated sums of a summable double family agree, with each
individually summable.** Given `g : ι × κ → E` summable, together with `HasSum` data for its row
sums (`row i = Σⱼ g(i,j)`) and column sums (`col j = Σᵢ g(i,j)`), `row` and `col` are themselves
summable and have the same total. -/
theorem tsum_fiberwise_eq_of_summable {ι κ E : Type*} [NormedAddCommGroup E]
    {g : ι × κ → E} {row : ι → E} {col : κ → E} (hg : Summable g)
    (hrow : ∀ i, HasSum (fun j => g (i, j)) (row i))
    (hcol : ∀ j, HasSum (fun i => g (i, j)) (col j)) :
    Summable row ∧ Summable col ∧ ∑' i, row i = ∑' j, col j := by
  have hg' : Summable (fun q : κ × ι => g q.swap) := hg.prod_symm
  have hswap : ∑' q : κ × ι, g q.swap = ∑' p : ι × κ, g p :=
    (Equiv.prodComm κ ι).tsum_eq g
  have haCol' : HasSum (fun q : κ × ι => g q.swap) (∑' p : ι × κ, g p) := by
    rw [← hswap]
    exact hg'.hasSum
  have haRow : HasSum row (∑' p, g p) := hg.hasSum.prod_fiberwise hrow
  have haCol : HasSum col (∑' p, g p) := haCol'.prod_fiberwise hcol
  exact ⟨haRow.summable, haCol.summable, haRow.tsum_eq.trans haCol.tsum_eq.symm⟩
