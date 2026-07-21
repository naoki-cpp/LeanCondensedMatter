import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.GroupTheory.Perm.Fin

set_option linter.style.header false

/-!
# `Pairing n`: the type, its finite enumeration, and normalized pairs

A perfect pairing of `Fin (2 * n)` is represented by its partner permutation: a fixed-point-free
involution. Mathlib supplies finite permutations but no naturally suitable bundled perfect-pairing
type with the linear order needed for crossing signs, so this file owns only that small predicate.
This representation enumerates `(2 * n)!` permutations and filters the valid ones, instead of
enumerating the powerset of all possible ordered pairs. It also gives the later Bloch–de Dominicis
induction direct access to the unique partner of every operator position.

`Pairing.pairs` normalizes each partner orbit to `(a, b)` with `a < b`, one per orbit
(`Pairing.mem_pairs_iff`/`pair_or_reverse_mem`/`pairs_normalized`).

The declarations keep their `SecondQuantization.Common.BlochDeDominicis` namespace, matching every
other file in this directory.
-/

namespace SecondQuantization
namespace Common
namespace BlochDeDominicis

/-- A permutation represents a perfect pairing when it is involutive and has no fixed point. -/
def IsPairing {n : ℕ} (partner : Equiv.Perm (Fin (2 * n))) : Prop :=
  Function.Involutive partner ∧ ∀ i, partner i ≠ i

instance decidableIsPairing {n : ℕ} (partner : Equiv.Perm (Fin (2 * n))) :
    Decidable (IsPairing partner) :=
  inferInstanceAs (Decidable (
    (∀ i, partner (partner i) = i) ∧ ∀ i, partner i ≠ i))

/-- A perfect pairing of the ordered positions `Fin (2 * n)`, represented through the stable
`partner` interface rather than exposing the subtype used for finite enumeration. -/
structure Pairing (n : ℕ) where
  partner : Equiv.Perm (Fin (2 * n))
  partner_involutive : Function.Involutive partner
  partner_ne_self : ∀ i, partner i ≠ i

/-- The internal equivalence used to enumerate `Pairing n` through finite permutations. -/
private def pairingEquivSubtype (n : ℕ) :
    Pairing n ≃ {partner : Equiv.Perm (Fin (2 * n)) // IsPairing partner} where
  toFun pairing :=
    ⟨pairing.partner, pairing.partner_involutive, pairing.partner_ne_self⟩
  invFun pairing :=
    { partner := pairing.1
      partner_involutive := pairing.2.1
      partner_ne_self := pairing.2.2 }
  left_inv pairing := by
    cases pairing
    rfl
  right_inv pairing := by
    apply Subtype.ext
    rfl

instance (n : ℕ) : Fintype (Pairing n) :=
  Fintype.ofEquiv {partner : Equiv.Perm (Fin (2 * n)) // IsPairing partner}
    (pairingEquivSubtype n).symm

instance (n : ℕ) : DecidableEq (Pairing n) :=
  Equiv.decidableEq (pairingEquivSubtype n)

@[ext]
theorem Pairing.ext {left right : Pairing n} (h : left.partner = right.partner) :
    left = right := by
  cases left
  cases right
  cases h
  rfl

@[simp]
theorem Pairing.partner_partner (pairing : Pairing n) (i : Fin (2 * n)) :
    pairing.partner (pairing.partner i) = i :=
  pairing.partner_involutive i

theorem Pairing.partner_ne (pairing : Pairing n) (i : Fin (2 * n)) :
    pairing.partner i ≠ i :=
  pairing.partner_ne_self i

/-- Construct the stable `Pairing` interface from an internally checked partner permutation. -/
def Pairing.ofPartner (partner : Equiv.Perm (Fin (2 * n))) (hpartner : IsPairing partner) :
    Pairing n where
  partner := partner
  partner_involutive := hpartner.1
  partner_ne_self := hpartner.2

/-- The finite enumeration of all perfect pairings of `Fin (2 * n)`. -/
def allPairings (n : ℕ) : Finset (Pairing n) := Finset.univ

@[simp]
theorem mem_allPairings (pairing : Pairing n) : pairing ∈ allPairings n := by
  simp [allPairings]

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

/-- Every position occurs in its normalized pair, either as the left or the right endpoint. -/
theorem Pairing.pair_or_reverse_mem {n : ℕ} (pairing : Pairing n) (i : Fin (2 * n)) :
    (i, pairing.partner i) ∈ pairing.pairs ∨
      (pairing.partner i, i) ∈ pairing.pairs := by
  by_cases h : i < pairing.partner i
  · left
    exact pairing.mem_pairs_iff i (pairing.partner i) |>.2 ⟨h, rfl⟩
  · right
    apply pairing.mem_pairs_iff (pairing.partner i) i |>.2
    exact ⟨lt_of_le_of_ne (le_of_not_gt h) (pairing.partner_ne i),
      pairing.partner_partner i⟩

/-- Every pair emitted by `Pairing.pairs` is normalized. -/
theorem Pairing.pairs_normalized {n : ℕ} (pairing : Pairing n)
    {pair : Fin (2 * n) × Fin (2 * n)} (hpair : pair ∈ pairing.pairs) :
    pair.1 < pair.2 := by
  rcases Finset.mem_image.mp hpair with ⟨i, hi, rfl⟩
  exact (Finset.mem_filter.mp hi).2

end BlochDeDominicis
end Common
end SecondQuantization
