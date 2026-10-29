module

public import Mathlib.Data.Finset.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

public section

set_option linter.style.header false

/-!
# Counting a filtered product by summing over the left coordinate

For finite sets `S` and `T` (possibly of different element types) and a relation `R`, the number
of pairs `(p, q) ∈ S × T` satisfying `R p q` equals the sum, over `p ∈ S`, of the number
of `q ∈ T` satisfying `R p q`. The original self-product identity is an immediate
specialization. This counting law is independent of pairing or crossing structures.
-/

theorem Finset.card_filter_product_eq_sum_card_filter {α β : Type*}
    (S : Finset α) (T : Finset β) (R : α → β → Prop) [DecidableRel R] :
    ((S.product T).filter fun pq => R pq.1 pq.2).card =
      ∑ p ∈ S, (T.filter fun q => R p q).card := by
  rw [Finset.card_filter]
  change (∑ i ∈ S ×ˢ T, if R i.1 i.2 then 1 else 0) =
    ∑ p ∈ S, (T.filter fun q => R p q).card
  rw [Finset.sum_product]
  simp_rw [Finset.card_filter]
