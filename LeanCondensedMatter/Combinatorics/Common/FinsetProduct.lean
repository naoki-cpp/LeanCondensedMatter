import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option linter.style.header false

/-!
# Counting a filtered self-product by summing over the left coordinate

For a finite set `T` and a binary relation `R`, the number of pairs `(p, q) ∈ T × T` satisfying
`R p q` equals the sum, over `p ∈ T`, of the number of `q ∈ T` with `R p q` — a `Finset.card`
counterpart of `Finset.sum_boole`-style double counting. General-purpose (no dependency on
`Pairing`/`Crosses` or any other project-specific structure); originally proved inline in
`Combinatorics/PerfectPairing/Crossing.lean`'s `card_filter_crosses_product_eq_sum` for the
specific relation `Crosses`, which now specializes this lemma instead.
-/

theorem Finset.card_filter_product_eq_sum_card_filter {α : Type*}
    (T : Finset α) (R : α → α → Prop) [DecidableRel R] :
    ((T.product T).filter fun pq => R pq.1 pq.2).card =
      ∑ p ∈ T, (T.filter fun q => R p q).card := by
  classical
  have hmaps : Set.MapsTo (Prod.fst : α × α → α)
      (((T.product T).filter (fun pp => R pp.1 pp.2) : Finset (α × α)) : Set (α × α))
      (T : Set α) := by
    intro pp hpp
    simp only [Finset.coe_filter, Finset.product_eq_sprod, Finset.mem_product,
      Set.mem_setOf_eq] at hpp
    exact hpp.1.1
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro p _
  have himg :
      ((T.product T).filter (fun pp => R pp.1 pp.2)).filter (fun pp => pp.1 = p) =
        (T.filter (fun q => R p q)).image (fun q => (p, q)) := by
    ext pp
    simp only [Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_image]
    constructor
    · rintro ⟨⟨⟨-, h2⟩, hR⟩, rfl⟩
      exact ⟨pp.2, ⟨h2, hR⟩, rfl⟩
    · rintro ⟨q, ⟨hq, hR⟩, rfl⟩
      exact ⟨⟨⟨‹p ∈ T›, hq⟩, hR⟩, rfl⟩
  rw [himg, Finset.card_image_of_injective _ fun a b h => by simpa using h]
