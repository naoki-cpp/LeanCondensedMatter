import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Order.Hom.Basic

set_option linter.style.header false

/-!
# Perfect pairings on arbitrary types and ordered finite positions

`PairingOn α` bundles a fixed-point-free involution on an arbitrary type `α`.
`Pairing n` is its ordered finite specialization to `Fin (2 * n)`, where the linear order supports
crossings and recursive finite combinatorics. Normalized pairs are available on any finite
linear order.

Mathlib supplies finite permutations but no naturally suitable bundled fixed-point-free involution
for this use. The finite specialization enumerates permutations of `Fin (2 * n)` and filters the
valid ones, while the generic bundle remains independent of finiteness and ordering.

`PairingOn.pairs` normalizes each finite ordered partner orbit to `(a, b)` with `a < b`, one per
orbit.
-/

namespace Combinatorics

/-- A permutation represents pairing data when it is involutive and has no fixed point. -/
def IsPairing {α : Type*} (partner : Equiv.Perm α) : Prop :=
  Function.Involutive partner ∧ ∀ i, partner i ≠ i

instance decidableIsPairing {α : Type*} [Fintype α] [DecidableEq α]
    (partner : Equiv.Perm α) : Decidable (IsPairing partner) :=
  inferInstanceAs (Decidable (
    (∀ i, partner (partner i) = i) ∧ ∀ i, partner i ≠ i))

/-- A perfect pairing on an arbitrary type: a fixed-point-free involutive permutation. -/
structure PairingOn (α : Type*) where
  /-- The fixed-point-free involution sending each element to its paired partner. -/
  partner : Equiv.Perm α
  partner_involutive : Function.Involutive partner
  partner_ne : ∀ i, partner i ≠ i

/-- A perfect pairing of the ordered positions `Fin (2 * n)`. The finite specialization supports first-pair recursion and position-indexed permutation signs. -/
abbrev Pairing (n : ℕ) := PairingOn (Fin (2 * n))

/-- The internal equivalence used to enumerate finite `PairingOn` values through permutations. -/
private def pairingOnEquivSubtype (α : Type*) :
    PairingOn α ≃ {partner : Equiv.Perm α // IsPairing partner} where
  toFun pairing :=
    ⟨pairing.partner, pairing.partner_involutive, pairing.partner_ne⟩
  invFun pairing :=
    { partner := pairing.1
      partner_involutive := pairing.2.1
      partner_ne := pairing.2.2 }
  left_inv pairing := by
    cases pairing
    rfl
  right_inv pairing := Subtype.ext rfl

instance {α : Type*} [Fintype α] [DecidableEq α] : Fintype (PairingOn α) :=
  Fintype.ofEquiv {partner : Equiv.Perm α // IsPairing partner}
    (pairingOnEquivSubtype α).symm

instance {α : Type*} [Fintype α] [DecidableEq α] : DecidableEq (PairingOn α) :=
  Equiv.decidableEq (pairingOnEquivSubtype α)

@[ext]
theorem PairingOn.ext {α : Type*} {left right : PairingOn α}
    (h : left.partner = right.partner) : left = right := by
  cases left
  cases right
  cases h
  rfl

@[simp]
theorem PairingOn.partner_partner {α : Type*} (pairing : PairingOn α) (i : α) :
    pairing.partner (pairing.partner i) = i :=
  pairing.partner_involutive i

/-- Construct a pairing bundle from an internally checked fixed-point-free involution. -/
def PairingOn.ofPartner {α : Type*} (partner : Equiv.Perm α) (hpartner : IsPairing partner) :
    PairingOn α where
  partner := partner
  partner_involutive := hpartner.1
  partner_ne := hpartner.2

/-- The disjoint sum of two pairings. -/
def PairingOn.sumCongr {α β : Type*} (left : PairingOn α) (right : PairingOn β) :
    PairingOn (α ⊕ β) :=
  PairingOn.ofPartner (Equiv.sumCongr left.partner right.partner) (by
    constructor
    · rintro (x | x)
      · exact congrArg Sum.inl (left.partner_involutive x)
      · exact congrArg Sum.inr (right.partner_involutive x)
    · rintro (x | x)
      · exact fun h => left.partner_ne x (Sum.inl.inj h)
      · exact fun h => right.partner_ne x (Sum.inr.inj h))

@[simp]
theorem PairingOn.sumCongr_partner_inl {α β : Type*}
    (left : PairingOn α) (right : PairingOn β) (x : α) :
    (left.sumCongr right).partner (Sum.inl x) = Sum.inl (left.partner x) := by
  rfl

@[simp]
theorem PairingOn.sumCongr_partner_inr {α β : Type*}
    (left : PairingOn α) (right : PairingOn β) (x : β) :
    (left.sumCongr right).partner (Sum.inr x) = Sum.inr (right.partner x) := by
  rfl

/-- The dependent sum of a family of pairings. -/
def PairingOn.sigmaCongrRight {ι : Type*} {β : ι → Type*}
    (F : ∀ i, PairingOn (β i)) : PairingOn (Σ i, β i) :=
  PairingOn.ofPartner (Equiv.sigmaCongrRight fun i => (F i).partner) (by
    constructor
    · rintro ⟨i, x⟩
      simp [(F i).partner_involutive x]
    · rintro ⟨i, x⟩
      simp only [Equiv.sigmaCongrRight_apply, ne_eq, Sigma.mk.injEq, heq_eq_eq, true_and]
      exact (F i).partner_ne x)

@[simp]
theorem PairingOn.sigmaCongrRight_partner {ι : Type*} {β : ι → Type*}
    (F : ∀ i, PairingOn (β i)) (i : ι) (x : β i) :
    (PairingOn.sigmaCongrRight F).partner ⟨i, x⟩ = ⟨i, (F i).partner x⟩ := by
  rfl

/-- The normalized ordered pairs `(i, partner i)` with `i < partner i`, one per partner orbit. -/
def PairingOn.pairs {α : Type*} [Fintype α] [LinearOrder α] (pairing : PairingOn α) :
    Finset (α × α) :=
  ((Finset.univ : Finset α).filter fun i => i < pairing.partner i).image fun i =>
    (i, pairing.partner i)

/-- Membership in `pairs` is characterized entirely through the stable `partner` interface. -/
theorem PairingOn.mem_pairs_iff {α : Type*} [Fintype α] [LinearOrder α]
    (pairing : PairingOn α) (i j : α) :
    (i, j) ∈ pairing.pairs ↔ i < j ∧ pairing.partner i = j := by
  simp only [PairingOn.pairs, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hk, hpair⟩
    have hki : k = i := congrArg Prod.fst hpair
    subst k
    have hp : pairing.partner i = j := congrArg Prod.snd hpair
    exact ⟨by simpa [hp] using hk, hp⟩
  · rintro ⟨hij, hp⟩
    refine ⟨i, ?_, ?_⟩
    · simpa [hp] using hij
    · simp [hp]

/-- If an order embedding intertwines two pairing partner maps, mapping both endpoints preserves and
reflects normalized pair membership. -/
theorem PairingOn.mem_pairs_map_iff {α β : Type*}
    [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β]
    (small : PairingOn α) (big : PairingOn β)
    (e : α ↪o β)
    (hpartner : ∀ i, big.partner (e i) = e (small.partner i))
    (a b : α) :
    (e a, e b) ∈ big.pairs ↔ (a, b) ∈ small.pairs := by
  rw [PairingOn.mem_pairs_iff, PairingOn.mem_pairs_iff]
  constructor
  · rintro ⟨hab, hp⟩
    refine ⟨e.lt_iff_lt.mp hab, ?_⟩
    apply e.injective
    calc
      e (small.partner a) = big.partner (e a) := (hpartner a).symm
      _ = e b := hp
  · rintro ⟨hab, hp⟩
    refine ⟨e.lt_iff_lt.mpr hab, ?_⟩
    rw [hpartner a, hp]

/-- Every pair emitted by `PairingOn.pairs` is normalized. -/
theorem PairingOn.pairs_normalized {α : Type*} [Fintype α] [LinearOrder α]
    (pairing : PairingOn α) {pair : α × α} (hpair : pair ∈ pairing.pairs) :
    pair.1 < pair.2 := by
  rcases Finset.mem_image.mp hpair with ⟨i, hi, rfl⟩
  exact (Finset.mem_filter.mp hi).2

open scoped BigOperators

/-- Evaluate a perfect pairing from a global scalar weight and a scalar kernel on its pair
endpoints. -/
def PairingOn.evaluation {R α : Type*} [CommMonoid R] [Fintype α] [LinearOrder α]
    (pairing : PairingOn α) (weight : R) (pairValue : α → α → R) : R :=
  weight * ∏ pr ∈ pairing.pairs, pairValue pr.1 pr.2

/-- The pair containing position `0`, i.e. `(0, partner 0)`. -/
def Pairing.firstPair {n : ℕ} (pairing : Pairing (n + 1)) :
    Fin (2 * (n + 1)) × Fin (2 * (n + 1)) :=
  (0, pairing.partner 0)

theorem Pairing.firstPair_mem_pairs {n : ℕ} (pairing : Pairing (n + 1)) :
    pairing.firstPair ∈ pairing.pairs := by
  apply (pairing.mem_pairs_iff 0 (pairing.partner 0)).2
  exact ⟨lt_of_le_of_ne (Fin.zero_le _) (Ne.symm (pairing.partner_ne 0)), rfl⟩

end Combinatorics
