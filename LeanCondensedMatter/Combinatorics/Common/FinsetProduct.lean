import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option linter.style.header false

/-!
# Counting a filtered self-product by summing over the left coordinate

For a finite set `T` and a binary relation `R`, the number of pairs `(p, q) ∈ T × T` satisfying
`R p q` equals the sum, over `p ∈ T`, of the number of `q ∈ T` with `R p q` — a `Finset.card`
counterpart of `Finset.sum_boole`-style double counting. This statement is general-purpose and
independent of project-specific pairing or crossing structures.
-/

theorem Finset.card_filter_product_eq_sum_card_filter {α : Type*}
    (T : Finset α) (R : α → α → Prop) [DecidableRel R] :
    ((T.product T).filter fun pq => R pq.1 pq.2).card =
      ∑ p ∈ T, (T.filter fun q => R p q).card := by
  simp_rw [Finset.card_filter, Finset.sum_product]
