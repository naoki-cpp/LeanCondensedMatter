import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.GroupTheory.Perm.Fin

set_option linter.style.header false

/-!
# Perfect pairings on arbitrary types and ordered finite positions

`PairingOn α` bundles a fixed-point-free involution on an arbitrary type `α`. The traditional
`Pairing n` is its ordered finite specialization to `Fin (2 * n)`, where the linear order supports
normalized pairs, crossings, and recursive finite combinatorics.

Mathlib supplies finite permutations but no naturally suitable bundled fixed-point-free involution
for this use. The finite specialization enumerates permutations of `Fin (2 * n)` and filters the
valid ones, while the generic bundle remains independent of finiteness and ordering.

`Pairing.pairs` normalizes each finite ordered partner orbit to `(a, b)` with `a < b`, one per
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

/-- A perfect pairing of the ordered positions `Fin (2 * n)`. Ordering-dependent notions such as
normalized pairs and crossing signs live on this finite specialization. -/
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

/-- The finite enumeration of all perfect pairings of `Fin (2 * n)`. -/
def allPairings (n : ℕ) : Finset (Pairing n) := Finset.univ

/-- The normalized ordered pairs `(i, partner i)` with `i < partner i`, one per partner orbit. -/
def Pairing.pairs {n : ℕ} (pairing : Pairing n) :
    Finset (Fin (2 * n) × Fin (2 * n)) :=
  ((Finset.univ : Finset (Fin (2 * n))).filter fun i => i < pairing.partner i).image fun i =>
    (i, pairing.partner i)

/-- Membership in `pairs` is characterized entirely through the stable `partner` interface. -/
theorem Pairing.mem_pairs_iff {n : ℕ} (pairing : Pairing n) (i j : Fin (2 * n)) :
    (i, j) ∈ pairing.pairs ↔ i < j ∧ pairing.partner i = j := by
  simp only [Pairing.pairs, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
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

/-- Every pair emitted by `Pairing.pairs` is normalized. -/
theorem Pairing.pairs_normalized {n : ℕ} (pairing : Pairing n)
    {pair : Fin (2 * n) × Fin (2 * n)} (hpair : pair ∈ pairing.pairs) :
    pair.1 < pair.2 := by
  rcases Finset.mem_image.mp hpair with ⟨i, hi, rfl⟩
  exact (Finset.mem_filter.mp hi).2

end Combinatorics
