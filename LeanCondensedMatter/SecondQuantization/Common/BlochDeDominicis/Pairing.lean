import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.DeletedPositions
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.GroupTheory.Perm.Fin

set_option linter.style.header false

/-!
# Pairings for the finite-temperature Bloch--de Dominicis theorem

The target of this project is the finite-temperature Bloch--de Dominicis factorization of
free/quasifree Gibbs expectations, not the vacuum-expectation Wick theorem or an arbitrary
interacting thermal state.  The namespace and module name make that distinction explicit even
though the finite pairing combinatorics itself does not depend on a temperature parameter.

A perfect pairing of `Fin (2 * n)` is represented by its partner permutation: a fixed-point-free
involution.  Mathlib supplies finite permutations but no naturally suitable bundled perfect-pairing
type with the linear order needed for crossing signs, so this file owns only that small predicate.
This representation enumerates `(2 * n)!` permutations and filters the valid ones, instead of
enumerating the powerset of all possible ordered pairs.  It also gives the later Bloch--de Dominicis
induction direct access to the unique partner of every operator position.

Each partner orbit is normalized to `(a, b)` with `a < b`.  Two normalized pairs cross when
`a < c < b < d`; `crossingCount` counts these. The statistics-dependent exchange weight
`ζ ^ crossingCount` itself — `ζ = +1` for bosons, `ζ = -1` for fermions — is *not* defined here; see
`Common/BlochDeDominicis/PairingWeight.lean`.

This file is purely combinatorial and has no `Statistics`/`ℂ` dependency at all: it defines neither
operator-valued time ordering, thermal contractions, thermal expectations, the exchange-statistics
weight, nor the Bloch--de Dominicis factorization theorem itself, and it imports neither
statistics-specific implementation directory.
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

/-- Restrict a pairing partner permutation to the positions left after removing `0` and its
partner.  The order-isomorphism back to `Fin (2 * n)` is applied by `eraseZeroPair`. -/
def Pairing.restrictedPartner {n : ℕ} (pairing : Pairing (n + 1))
    (hzero : (0 : Fin (2 * (n + 1))) ≠ pairing.partner 0) :
    deletedPositions n (pairing.partner 0) hzero ≃
      deletedPositions n (pairing.partner 0) hzero where
  toFun := fun x => by
    have hxj : (x : Fin (2 * (n + 1))) ≠ pairing.partner 0 :=
      (Finset.mem_erase.mp x.property).1
    have hx0 : (x : Fin (2 * (n + 1))) ≠ 0 :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp x.property).2).1
    have hpxj : pairing.partner x ≠ pairing.partner 0 := by
      intro h
      apply hx0
      calc
        (x : Fin (2 * (n + 1))) = pairing.partner (pairing.partner x) :=
          (pairing.partner_partner x).symm
        _ = pairing.partner (pairing.partner 0) := by rw [h]
        _ = 0 := pairing.partner_partner 0
    have hpx0 : pairing.partner x ≠ 0 := by
      intro h
      apply hxj
      calc
        (x : Fin (2 * (n + 1))) = pairing.partner (pairing.partner x) :=
          (pairing.partner_partner x).symm
        _ = pairing.partner 0 := by rw [h]
    exact ⟨pairing.partner x,
      Finset.mem_erase.mpr ⟨hpxj, Finset.mem_erase.mpr ⟨hpx0, Finset.mem_univ _⟩⟩⟩
  invFun := fun x => by
    have hxj : (x : Fin (2 * (n + 1))) ≠ pairing.partner 0 :=
      (Finset.mem_erase.mp x.property).1
    have hx0 : (x : Fin (2 * (n + 1))) ≠ 0 :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp x.property).2).1
    have hpxj : pairing.partner x ≠ pairing.partner 0 := by
      intro h
      apply hx0
      calc
        (x : Fin (2 * (n + 1))) = pairing.partner (pairing.partner x) :=
          (pairing.partner_partner x).symm
        _ = pairing.partner (pairing.partner 0) := by rw [h]
        _ = 0 := pairing.partner_partner 0
    have hpx0 : pairing.partner x ≠ 0 := by
      intro h
      apply hxj
      calc
        (x : Fin (2 * (n + 1))) = pairing.partner (pairing.partner x) :=
          (pairing.partner_partner x).symm
        _ = pairing.partner 0 := by rw [h]
    exact ⟨pairing.partner x,
      Finset.mem_erase.mpr ⟨hpxj, Finset.mem_erase.mpr ⟨hpx0, Finset.mem_univ _⟩⟩⟩
  left_inv x := by
    apply Subtype.ext
    exact pairing.partner_partner x
  right_inv x := by
    apply Subtype.ext
    exact pairing.partner_partner x

@[simp]
theorem Pairing.restrictedPartner_partner_partner {n : ℕ} (pairing : Pairing (n + 1))
    (hzero : (0 : Fin (2 * (n + 1))) ≠ pairing.partner 0)
    (x : deletedPositions n (pairing.partner 0) hzero) :
    pairing.restrictedPartner hzero (pairing.restrictedPartner hzero x) = x := by
  apply Subtype.ext
  exact pairing.partner_partner x

/-- Remove position `0` and its partner, reindexing the remaining positions in increasing order.

The resulting pairing is the combinatorial deletion step used by the finite-temperature
Bloch--de Dominicis induction. -/
noncomputable def Pairing.eraseZeroPair {n : ℕ} (pairing : Pairing (n + 1)) : Pairing n := by
  let hzero : (0 : Fin (2 * (n + 1))) ≠ pairing.partner 0 :=
    Ne.symm (pairing.partner_ne 0)
  let e := deletedPositionsOrderIso n (pairing.partner 0) hzero
  let r := pairing.restrictedPartner hzero
  let newPartner : Equiv.Perm (Fin (2 * n)) :=
    e.toEquiv.trans (r.trans e.symm.toEquiv)
  refine
    { partner := newPartner
      partner_involutive := ?_
      partner_ne_self := ?_ }
  · intro i
    dsimp [newPartner]
    rw [e.apply_symm_apply]
    rw [Pairing.restrictedPartner_partner_partner]
    exact e.symm_apply_apply i
  · intro i hi
    have hfixed : r (e i) = e i := by
      have h := congrArg e hi
      simpa [newPartner] using h
    have hpartner : pairing.partner (e i) = (e i : Fin (2 * (n + 1))) := by
      exact congrArg Subtype.val hfixed
    exact pairing.partner_ne (e i) hpartner

theorem Pairing.eraseZeroPair_partner_apply {n : ℕ} (pairing : Pairing (n + 1))
    (i : Fin (2 * n)) :
    (pairing.eraseZeroPair).partner i =
      let hzero : (0 : Fin (2 * (n + 1))) ≠ pairing.partner 0 :=
        Ne.symm (pairing.partner_ne 0)
      let e := deletedPositionsOrderIso n (pairing.partner 0) hzero
      e.symm (pairing.restrictedPartner hzero (e i)) := by
  simp [Pairing.eraseZeroPair]

/-- The order isomorphism used by `eraseZeroPair`, exposed as a named interface for later
induction lemmas. -/
noncomputable def Pairing.eraseZeroOrderIso {n : ℕ} (pairing : Pairing (n + 1)) :
    Fin (2 * n) ≃o
      deletedPositions n (pairing.partner 0)
        (Ne.symm (pairing.partner_ne 0)) :=
  deletedPositionsOrderIso n (pairing.partner 0) (Ne.symm (pairing.partner_ne 0))

@[simp]
theorem Pairing.eraseZeroOrderIso_partner {n : ℕ} (pairing : Pairing (n + 1))
    (i : Fin (2 * n)) :
    ((pairing.eraseZeroOrderIso ((pairing.eraseZeroPair).partner i) :
      Fin (2 * (n + 1)))) =
    pairing.partner (pairing.eraseZeroOrderIso i) := by
  simp [Pairing.eraseZeroOrderIso, Pairing.eraseZeroPair_partner_apply]
  rfl

theorem Pairing.eraseZeroPair_mem_pairs_iff {n : ℕ} (pairing : Pairing (n + 1))
    (i k : Fin (2 * n)) :
    (i, k) ∈ (pairing.eraseZeroPair).pairs ↔
      ((pairing.eraseZeroOrderIso i : Fin (2 * (n + 1))),
        (pairing.eraseZeroOrderIso k : Fin (2 * (n + 1)))) ∈ pairing.pairs := by
  rw [Pairing.mem_pairs_iff, Pairing.mem_pairs_iff]
  constructor
  · rintro ⟨hik, hpartner⟩
    refine ⟨pairing.eraseZeroOrderIso.strictMono hik, ?_⟩
    have hp := Pairing.eraseZeroOrderIso_partner pairing i
    rw [hpartner] at hp
    exact hp.symm
  · rintro ⟨hik, hpartner⟩
    have hik' : i < k := by
      have h := pairing.eraseZeroOrderIso.symm.strictMono hik
      simpa using h
    refine ⟨hik', ?_⟩
    apply pairing.eraseZeroOrderIso.injective
    apply Subtype.ext
    calc
      pairing.eraseZeroOrderIso ((pairing.eraseZeroPair).partner i) =
          pairing.partner (pairing.eraseZeroOrderIso i) :=
        Pairing.eraseZeroOrderIso_partner pairing i
      _ = pairing.eraseZeroOrderIso k := hpartner

/-- Every pair emitted by `Pairing.pairs` is normalized. -/
theorem Pairing.pairs_normalized {n : ℕ} (pairing : Pairing n)
    {pair : Fin (2 * n) × Fin (2 * n)} (hpair : pair ∈ pairing.pairs) :
    pair.1 < pair.2 := by
  rcases Finset.mem_image.mp hpair with ⟨i, hi, rfl⟩
  exact (Finset.mem_filter.mp hi).2

/-- The normalized pair `(a, b)` crosses `(c, d)` when `a < c < b < d`. -/
def Crosses {n : ℕ} (left right : Fin (2 * n) × Fin (2 * n)) : Prop :=
  left.1 < right.1 ∧ right.1 < left.2 ∧ left.2 < right.2

instance decidableCrosses {n : ℕ}
    (left right : Fin (2 * n) × Fin (2 * n)) : Decidable (Crosses left right) :=
  inferInstanceAs (Decidable (
    left.1 < right.1 ∧ right.1 < left.2 ∧ left.2 < right.2))

theorem Pairing.eraseZeroPair_crosses_iff {n : ℕ} (pairing : Pairing (n + 1))
    (i k p q : Fin (2 * n)) :
    Crosses (i, k) (p, q) ↔
      Crosses
        ((pairing.eraseZeroOrderIso i : Fin (2 * (n + 1))),
          (pairing.eraseZeroOrderIso k : Fin (2 * (n + 1))))
        ((pairing.eraseZeroOrderIso p : Fin (2 * (n + 1))),
          (pairing.eraseZeroOrderIso q : Fin (2 * (n + 1)))) := by
  constructor
  · rintro ⟨hik, hkp, hpq⟩
    exact ⟨pairing.eraseZeroOrderIso.strictMono hik,
      pairing.eraseZeroOrderIso.strictMono hkp,
      pairing.eraseZeroOrderIso.strictMono hpq⟩
  · rintro ⟨hik, hkp, hpq⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa using pairing.eraseZeroOrderIso.symm.strictMono hik
    · simpa using pairing.eraseZeroOrderIso.symm.strictMono hkp
    · simpa using pairing.eraseZeroOrderIso.symm.strictMono hpq

/-- The number of geometric crossings.  `Crosses` fixes the order of the left endpoints, so each
crossing is counted exactly once. -/
def Pairing.crossingCount {n : ℕ} (pairing : Pairing n) : ℕ :=
  ((pairing.pairs.product pairing.pairs).filter fun pairPair =>
    Crosses pairPair.1 pairPair.2).card

/-- The pair containing position `0`, i.e. `(0, partner 0)`. -/
def Pairing.firstPair {n : ℕ} (pairing : Pairing (n + 1)) :
    Fin (2 * (n + 1)) × Fin (2 * (n + 1)) :=
  (0, pairing.partner 0)

theorem Pairing.firstPair_mem_pairs {n : ℕ} (pairing : Pairing (n + 1)) :
    pairing.firstPair ∈ pairing.pairs := by
  apply (pairing.mem_pairs_iff 0 (pairing.partner 0)).2
  exact ⟨lt_of_le_of_ne (Fin.zero_le _) (Ne.symm (pairing.partner_ne 0)), rfl⟩

/-- Every normalized pair other than `firstPair` has both endpoints away from `0` and its
partner: this is what lets `eraseZeroOrderIso.symm` be applied to it. -/
theorem Pairing.mem_pairs_endpoints_mem_deletedPositions {n : ℕ} (pairing : Pairing (n + 1))
    {p : Fin (2 * (n + 1)) × Fin (2 * (n + 1))} (hp : p ∈ pairing.pairs)
    (hne : p ≠ pairing.firstPair) :
    p.1 ∈ deletedPositions n (pairing.partner 0) (Ne.symm (pairing.partner_ne 0)) ∧
      p.2 ∈ deletedPositions n (pairing.partner 0) (Ne.symm (pairing.partner_ne 0)) := by
  obtain ⟨hlt, hpartner⟩ := (pairing.mem_pairs_iff p.1 p.2).1 (by simpa using hp)
  have h10 : p.1 ≠ 0 := by
    intro h
    apply hne
    have h2 : p.2 = pairing.partner 0 := by rw [← hpartner, h]
    change p = pairing.firstPair
    rw [Pairing.firstPair]
    exact Prod.ext h h2
  have h1j : p.1 ≠ pairing.partner 0 := by
    intro h
    apply h10
    have hp2 : p.2 = 0 := by
      have := hpartner
      rw [h] at this
      rw [pairing.partner_partner] at this
      exact this.symm
    have : (pairing.partner 0 : Fin (2 * (n + 1))) < 0 := by rw [← h]; exact hp2 ▸ hlt
    exact absurd this (by simp)
  have h20 : p.2 ≠ 0 := fun h => absurd (h ▸ hlt) (by simp)
  have h2j : p.2 ≠ pairing.partner 0 := by
    intro h
    apply h10
    have hinj : Function.Injective pairing.partner := pairing.partner.injective
    apply hinj
    rw [hpartner, h]
  refine ⟨?_, ?_⟩
  · simp [deletedPositions, Finset.mem_erase, h10, h1j]
  · simp [deletedPositions, Finset.mem_erase, h20, h2j]

/-- The number of pairs (other than `firstPair`) crossing `firstPair`. -/
def Pairing.crossingsWithFirstPair {n : ℕ} (pairing : Pairing (n + 1)) : ℕ :=
  (pairing.pairs.filter fun p => Crosses pairing.firstPair p).card

theorem not_crosses_firstPair {n : ℕ} (pairing : Pairing (n + 1))
    (p : Fin (2 * (n + 1)) × Fin (2 * (n + 1))) : ¬ Crosses p pairing.firstPair := by
  rintro ⟨h1, -, -⟩
  exact absurd h1 (by simp [Pairing.firstPair])

theorem not_crosses_self {n : ℕ} (p : Fin (2 * n) × Fin (2 * n)) : ¬ Crosses p p := by
  rintro ⟨h, -, -⟩
  exact absurd h (lt_irrefl _)

/-- A crossing-count as a product-filter card decomposes into a sum over the left endpoint. -/
theorem card_filter_crosses_product_eq_sum {n : ℕ} (T : Finset (Fin (2 * n) × Fin (2 * n))) :
    ((T.product T).filter (fun pp => Crosses pp.1 pp.2)).card =
      ∑ p ∈ T, (T.filter (fun q => Crosses p q)).card := by
  classical
  have hmaps : Set.MapsTo
      (Prod.fst : (Fin (2 * n) × Fin (2 * n)) × (Fin (2 * n) × Fin (2 * n)) →
        Fin (2 * n) × Fin (2 * n))
      (((T.product T).filter (fun pp => Crosses pp.1 pp.2) :
        Finset ((Fin (2 * n) × Fin (2 * n)) × (Fin (2 * n) × Fin (2 * n)))) : Set _)
      (T : Set (Fin (2 * n) × Fin (2 * n))) := by
    intro pp hpp
    simp only [Finset.coe_filter, Finset.product_eq_sprod, Finset.mem_product,
      Set.mem_setOf_eq] at hpp
    exact hpp.1.1
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro p _
  have himg :
      ((T.product T).filter (fun pp => Crosses pp.1 pp.2)).filter (fun pp => pp.1 = p) =
        (T.filter (fun q => Crosses p q)).image (fun q => (p, q)) := by
    ext pp
    simp only [Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_image]
    constructor
    · rintro ⟨⟨⟨-, h2⟩, hcross⟩, rfl⟩
      exact ⟨pp.2, ⟨h2, hcross⟩, rfl⟩
    · rintro ⟨q, ⟨hq, hcross⟩, rfl⟩
      exact ⟨⟨⟨‹p ∈ T›, hq⟩, hcross⟩, rfl⟩
  rw [himg, Finset.card_image_of_injective _ fun a b h => by simpa using h]

/-- The crossing count splits along the pair containing position `0`: crossings entirely among
the remaining pairs (`eraseZeroPair.crossingCount`) plus crossings with `firstPair`
(`crossingsWithFirstPair`). -/
theorem Pairing.crossingCount_eraseZeroPair {n : ℕ} (pairing : Pairing (n + 1)) :
    pairing.crossingCount =
      pairing.eraseZeroPair.crossingCount + pairing.crossingsWithFirstPair := by
  classical
  set F := pairing.firstPair with hF
  set S := pairing.pairs with hS
  set A := S.erase F with hA
  have hFmem : F ∈ S := pairing.firstPair_mem_pairs
  have hFnotA : F ∉ A := fun h => (Finset.mem_erase.mp h).1 rfl
  have hsplit : S = insert F A := (Finset.insert_erase hFmem).symm
  have hsum : pairing.crossingCount =
      (S.filter (fun q => Crosses F q)).card + ∑ p ∈ A, (S.filter (fun q => Crosses p q)).card := by
    rw [Pairing.crossingCount, ← hS, card_filter_crosses_product_eq_sum, hsplit,
      Finset.sum_insert hFnotA, ← hsplit]
  have hFterm : (S.filter (fun q => Crosses F q)).card = pairing.crossingsWithFirstPair := rfl
  have hAterm : ∀ p ∈ A, S.filter (fun q => Crosses p q) = A.filter (fun q => Crosses p q) := by
    intro p _
    rw [hsplit, Finset.filter_insert, if_neg (not_crosses_firstPair pairing p)]
  have hsum' : pairing.crossingCount =
      pairing.crossingsWithFirstPair + ∑ p ∈ A, (A.filter (fun q => Crosses p q)).card := by
    rw [hsum, hFterm]
    congr 1
    exact Finset.sum_congr rfl fun p hp => by rw [hAterm p hp]
  have hAcross : ((A.product A).filter (fun pp => Crosses pp.1 pp.2)).card =
      ∑ p ∈ A, (A.filter (fun q => Crosses p q)).card :=
    card_filter_crosses_product_eq_sum A
  have hbij :
      ((pairing.eraseZeroPair.pairs.product pairing.eraseZeroPair.pairs).filter
        (fun pp => Crosses pp.1 pp.2)).card =
      ((A.product A).filter (fun pp => Crosses pp.1 pp.2)).card := by
    classical
    let mapPair : Fin (2 * n) × Fin (2 * n) → Fin (2 * (n + 1)) × Fin (2 * (n + 1)) :=
      fun P => (pairing.eraseZeroOrderIso P.1, pairing.eraseZeroOrderIso P.2)
    have hmapPair_ne_zero : ∀ P : Fin (2 * n) × Fin (2 * n), (mapPair P).1 ≠ 0 := by
      intro P
      have := (pairing.eraseZeroOrderIso P.1).property
      simp only [deletedPositions, Finset.mem_erase] at this
      exact this.2.1
    apply Finset.card_bij
      (i := fun (PQ : (Fin (2 * n) × Fin (2 * n)) × (Fin (2 * n) × Fin (2 * n))) _ =>
        (mapPair PQ.1, mapPair PQ.2))
    · rintro ⟨P, Q⟩ hPQ
      simp only [Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product] at hPQ ⊢
      obtain ⟨⟨hP, hQ⟩, hcross⟩ := hPQ
      have hPmem : mapPair P ∈ S := by
        rw [hS]
        exact (pairing.eraseZeroPair_mem_pairs_iff P.1 P.2).1 (by simpa using hP)
      have hQmem : mapPair Q ∈ S := by
        rw [hS]
        exact (pairing.eraseZeroPair_mem_pairs_iff Q.1 Q.2).1 (by simpa using hQ)
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hA]
        exact Finset.mem_erase.2 ⟨fun h => hmapPair_ne_zero P (by rw [h]; rfl), hPmem⟩
      · rw [hA]
        exact Finset.mem_erase.2 ⟨fun h => hmapPair_ne_zero Q (by rw [h]; rfl), hQmem⟩
      · exact (pairing.eraseZeroPair_crosses_iff P.1 P.2 Q.1 Q.2).1 (by simpa using hcross)
    · rintro ⟨P, Q⟩ _ ⟨P', Q'⟩ _ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have hPeq : P = P' := by
        apply Prod.ext
        · exact pairing.eraseZeroOrderIso.injective (Subtype.ext (congrArg Prod.fst h1))
        · exact pairing.eraseZeroOrderIso.injective (Subtype.ext (congrArg Prod.snd h1))
      have hQeq : Q = Q' := by
        apply Prod.ext
        · exact pairing.eraseZeroOrderIso.injective (Subtype.ext (congrArg Prod.fst h2))
        · exact pairing.eraseZeroOrderIso.injective (Subtype.ext (congrArg Prod.snd h2))
      rw [hPeq, hQeq]
    · rintro ⟨p, q⟩ hpq
      simp only [Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product] at hpq
      obtain ⟨⟨hp, hq⟩, hcross⟩ := hpq
      have hpS : p ∈ S := (Finset.mem_erase.mp (hA ▸ hp)).2
      have hqS : q ∈ S := (Finset.mem_erase.mp (hA ▸ hq)).2
      have hpF : p ≠ F := (Finset.mem_erase.mp (hA ▸ hp)).1
      have hqF : q ≠ F := (Finset.mem_erase.mp (hA ▸ hq)).1
      obtain ⟨hp1, hp2⟩ := pairing.mem_pairs_endpoints_mem_deletedPositions hpS hpF
      obtain ⟨hq1, hq2⟩ := pairing.mem_pairs_endpoints_mem_deletedPositions hqS hqF
      refine ⟨(⟨(pairing.eraseZeroOrderIso.symm ⟨p.1, hp1⟩ : Fin (2 * n)),
          (pairing.eraseZeroOrderIso.symm ⟨p.2, hp2⟩ : Fin (2 * n))⟩,
        ⟨(pairing.eraseZeroOrderIso.symm ⟨q.1, hq1⟩ : Fin (2 * n)),
          (pairing.eraseZeroOrderIso.symm ⟨q.2, hq2⟩ : Fin (2 * n))⟩), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [pairing.eraseZeroPair_mem_pairs_iff]
          simp only [OrderIso.apply_symm_apply]
          rwa [Prod.mk.eta]
        · rw [pairing.eraseZeroPair_mem_pairs_iff]
          simp only [OrderIso.apply_symm_apply]
          rwa [Prod.mk.eta]
        · rw [pairing.eraseZeroPair_crosses_iff]
          simp only [OrderIso.apply_symm_apply]
          rwa [Prod.mk.eta, Prod.mk.eta]
      · simp only [mapPair, OrderIso.apply_symm_apply, Prod.mk.eta]
  rw [hsum', ← hAcross, Pairing.crossingCount, hbij]
  omega

/-- The number of positions strictly between `0` and its partner. -/
def Pairing.interveningPositionCount {n : ℕ} (pairing : Pairing (n + 1)) : ℕ :=
  (pairing.partner 0).val - 1

/-- `firstPair`'s crossings correspond exactly to intervening positions whose partner lies past
`partner 0`; the remaining intervening positions pair off amongst themselves and so contribute an
even count. Hence `crossingsWithFirstPair` and `interveningPositionCount` agree mod `2`. -/
theorem Pairing.crossingsWithFirstPair_mod_two {n : ℕ} (pairing : Pairing (n + 1)) :
    pairing.crossingsWithFirstPair % 2 = pairing.interveningPositionCount % 2 := by
  classical
  set j : Fin (2 * (n + 1)) := pairing.partner 0 with hj
  set I : Finset (Fin (2 * (n + 1))) := Finset.Ioo 0 j with hI
  set C : Finset (Fin (2 * (n + 1))) := I.filter (fun k => j < pairing.partner k) with hC
  set D : Finset (Fin (2 * (n + 1))) := I.filter (fun k => pairing.partner k < j) with hD
  have hpartner_ne0 : ∀ k ∈ I, pairing.partner k ≠ 0 := by
    intro k hk h
    have hkj : k = j := by
      have h' := congrArg pairing.partner h
      rwa [pairing.partner_partner, ← hj] at h'
    have hklt : k < j := (Finset.mem_Ioo.mp hk).2
    rw [hkj] at hklt
    exact lt_irrefl _ hklt
  have hpartner_nej : ∀ k ∈ I, pairing.partner k ≠ j := by
    intro k hk h
    have hk0 : (0 : Fin (2 * (n + 1))) < k := (Finset.mem_Ioo.mp hk).1
    have hk0' : k = 0 := by
      have heq : pairing.partner k = pairing.partner 0 := by rw [h, hj]
      exact pairing.partner.injective heq
    rw [hk0'] at hk0
    exact lt_irrefl _ hk0
  have hsplitI : I = D ∪ C := by
    ext k
    simp only [hD, hC, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hk
      rcases lt_trichotomy (pairing.partner k) j with h | h | h
      · exact Or.inl ⟨hk, h⟩
      · exact absurd h (hpartner_nej k hk)
      · exact Or.inr ⟨hk, h⟩
    · rintro (⟨hk, -⟩ | ⟨hk, -⟩) <;> exact hk
  have hdisjDC : Disjoint D C := by
    rw [Finset.disjoint_left]
    intro k hkD hkC
    exact absurd (Finset.mem_filter.mp hkD).2 (not_lt.mpr (Finset.mem_filter.mp hkC).2.le)
  have hCcard : C.card = pairing.crossingsWithFirstPair := by
    rw [Pairing.crossingsWithFirstPair]
    apply Finset.card_bij' (fun k _ => (k, pairing.partner k)) (fun pq _ => pq.1)
    · intro k hk
      simp only [hC, Finset.mem_filter, hI, Finset.mem_Ioo] at hk
      obtain ⟨⟨hk0, hkj⟩, hkgt⟩ := hk
      simp only [Finset.mem_filter]
      refine ⟨(pairing.mem_pairs_iff k (pairing.partner k)).2 ⟨?_, rfl⟩, ?_, ?_, ?_⟩
      · exact hkj.trans hkgt
      · exact hk0
      · exact hkj
      · exact hkgt
    · intro pq hpq
      simp only [Finset.mem_filter] at hpq
      obtain ⟨hpqmem, h1, h2, h3⟩ := hpq
      simp only [hC, Finset.mem_filter, hI, Finset.mem_Ioo]
      have hpartner : pairing.partner pq.1 = pq.2 := ((pairing.mem_pairs_iff pq.1 pq.2).1 hpqmem).2
      exact ⟨⟨h1, h2⟩, by rw [hpartner]; exact h3⟩
    · intro k _
      rfl
    · intro pq hpq
      simp only [Finset.mem_filter] at hpq
      obtain ⟨hpqmem, -, -, -⟩ := hpq
      have hpartner : pairing.partner pq.1 = pq.2 := ((pairing.mem_pairs_iff pq.1 pq.2).1 hpqmem).2
      exact Prod.ext rfl hpartner
  set A : Finset (Fin (2 * (n + 1))) := D.filter (fun k => k < pairing.partner k) with hA
  set B : Finset (Fin (2 * (n + 1))) := D.filter (fun k => pairing.partner k < k) with hB
  have hsplitD : D = A ∪ B := by
    ext k
    simp only [hA, hB, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hk
      rcases lt_trichotomy k (pairing.partner k) with h | h | h
      · exact Or.inl ⟨hk, h⟩
      · exact absurd h.symm (pairing.partner_ne k)
      · exact Or.inr ⟨hk, h⟩
    · rintro (⟨hk, -⟩ | ⟨hk, -⟩) <;> exact hk
  have hdisjAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro k hkA hkB
    exact absurd (Finset.mem_filter.mp hkA).2 (not_lt.mpr (Finset.mem_filter.mp hkB).2.le)
  have hAB : A.card = B.card := by
    apply Finset.card_bij' (fun k _ => pairing.partner k) (fun k _ => pairing.partner k)
    · intro k hk
      simp only [hA, Finset.mem_filter] at hk
      obtain ⟨hkD, hklt⟩ := hk
      simp only [hB, Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · simp only [hD, hI, Finset.mem_filter, Finset.mem_Ioo] at hkD ⊢
        obtain ⟨⟨h1, h2⟩, h3⟩ := hkD
        exact ⟨⟨h1.trans hklt, h3⟩, by rw [pairing.partner_partner]; exact h2⟩
      · rw [pairing.partner_partner]; exact hklt
    · intro k hk
      simp only [hB, Finset.mem_filter] at hk
      obtain ⟨hkD, hklt⟩ := hk
      simp only [hA, Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · simp only [hD, hI, Finset.mem_filter, Finset.mem_Ioo] at hkD ⊢
        obtain ⟨⟨h1, h2⟩, h3⟩ := hkD
        have hpos : (0 : Fin (2 * (n + 1))) < pairing.partner k :=
          lt_of_le_of_ne (Fin.zero_le _)
            (Ne.symm (hpartner_ne0 k (Finset.mem_Ioo.mpr ⟨h1, h2⟩)))
        exact ⟨⟨hpos, h3⟩, by rw [pairing.partner_partner]; exact h2⟩
      · rw [pairing.partner_partner]; exact hklt
    · intro k _
      exact pairing.partner_partner k
    · intro k _
      exact pairing.partner_partner k
  have hDcard : D.card = 2 * A.card := by
    rw [hsplitD, Finset.card_union_of_disjoint hdisjAB, hAB]
    ring
  have hIcard : I.card = D.card + C.card := by
    rw [hsplitI, Finset.card_union_of_disjoint hdisjDC]
  have hIcard' : I.card = pairing.interveningPositionCount := by
    rw [hI, Fin.card_Ioo, Pairing.interveningPositionCount, hj]
    simp
  have hfinal : pairing.interveningPositionCount = 2 * A.card + pairing.crossingsWithFirstPair := by
    rw [← hIcard', hIcard, hDcard, hCcard]
  omega

/-- Insert a new pair `(0, j)` ahead of a smaller pairing, reindexing it onto the positions left
after removing `0` and `j`. This is the constructive counterpart to `Pairing.eraseZeroPair` needed
to let the Bloch--de Dominicis induction build up a `Pairing (n + 1)` from a choice of `j` and a
smaller `Pairing n`, rather than only tearing one down; the round-trip laws connecting the two
directions are proved separately. -/
noncomputable def Pairing.insertFirstPair {n : ℕ} (pairing : Pairing n) (j : Fin (2 * (n + 1)))
    (hj : (0 : Fin (2 * (n + 1))) ≠ j) : Pairing (n + 1) := by
  let oi := deletedPositionsOrderIso n j hj
  let extended : Equiv.Perm (Fin (2 * (n + 1))) := pairing.partner.extendDomain oi.toEquiv
  have hext0 : extended (0 : Fin (2 * (n + 1))) = 0 :=
    Equiv.Perm.extendDomain_apply_not_subtype _ _ (by simp [deletedPositions])
  have hextj : extended j = j :=
    Equiv.Perm.extendDomain_apply_not_subtype _ _ (by simp [deletedPositions])
  have hextInv : ∀ x : Fin (2 * (n + 1)), extended (extended x) = x := by
    intro x
    by_cases hx : x ∈ deletedPositions n j hj
    · have h1 : extended x = (oi (pairing.partner (oi.symm ⟨x, hx⟩)) : Fin (2 * (n + 1))) :=
        Equiv.Perm.extendDomain_apply_subtype _ _ hx
      have hx2 : extended x ∈ deletedPositions n j hj := by
        rw [h1]; exact (oi (pairing.partner (oi.symm ⟨x, hx⟩))).property
      have h2 : extended (extended x) =
          (oi (pairing.partner (oi.symm ⟨extended x, hx2⟩)) : Fin (2 * (n + 1))) :=
        Equiv.Perm.extendDomain_apply_subtype _ _ hx2
      rw [h2]
      have hsymm : oi.symm ⟨extended x, hx2⟩ = pairing.partner (oi.symm ⟨x, hx⟩) := by
        apply oi.injective
        simp [h1]
      rw [hsymm, pairing.partner_partner]
      simp
    · have hx' : extended x = x := Equiv.Perm.extendDomain_apply_not_subtype _ _ hx
      rw [hx', hx']
  have hextNe : ∀ x : Fin (2 * (n + 1)), x ∈ deletedPositions n j hj → extended x ≠ x := by
    intro x hx h
    have h1 : extended x = (oi (pairing.partner (oi.symm ⟨x, hx⟩)) : Fin (2 * (n + 1))) :=
      Equiv.Perm.extendDomain_apply_subtype _ _ hx
    have h2 : oi (pairing.partner (oi.symm ⟨x, hx⟩)) = oi (oi.symm ⟨x, hx⟩) := by
      apply Subtype.ext
      rw [← h1, h]
      simp
    have h3 : pairing.partner (oi.symm ⟨x, hx⟩) = oi.symm ⟨x, hx⟩ := oi.injective h2
    exact pairing.partner_ne _ h3
  refine Pairing.ofPartner (Equiv.swap 0 j * extended) ⟨?_, ?_⟩
  · intro x
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    by_cases hx0 : x = 0
    · subst hx0
      rw [hext0, Equiv.swap_apply_left, hextj, Equiv.swap_apply_right]
    · by_cases hxj : x = j
      · subst hxj
        rw [hextj, Equiv.swap_apply_right, hext0, Equiv.swap_apply_left]
      · have hxmem : x ∈ deletedPositions n j hj := by simp [deletedPositions, hx0, hxj]
        have hex : extended x ∈ deletedPositions n j hj := by
          have h1 : extended x = (oi (pairing.partner (oi.symm ⟨x, hxmem⟩)) : Fin (2 * (n + 1))) :=
            Equiv.Perm.extendDomain_apply_subtype _ _ hxmem
          rw [h1]; exact (oi (pairing.partner (oi.symm ⟨x, hxmem⟩))).property
        rw [Equiv.swap_apply_of_ne_of_ne
          (Finset.mem_erase.mp (Finset.mem_erase.mp hex).2).1 (Finset.mem_erase.mp hex).1,
          hextInv, Equiv.swap_apply_of_ne_of_ne hx0 hxj]
  · intro x
    rw [Equiv.Perm.mul_apply]
    by_cases hx0 : x = 0
    · subst hx0
      rw [hext0, Equiv.swap_apply_left]
      exact Ne.symm hj
    · by_cases hxj : x = j
      · subst hxj
        rw [hextj, Equiv.swap_apply_right]
        exact hj
      · have hxmem : x ∈ deletedPositions n j hj := by simp [deletedPositions, hx0, hxj]
        have hex : extended x ∈ deletedPositions n j hj := by
          have h1 : extended x = (oi (pairing.partner (oi.symm ⟨x, hxmem⟩)) : Fin (2 * (n + 1))) :=
            Equiv.Perm.extendDomain_apply_subtype _ _ hxmem
          rw [h1]; exact (oi (pairing.partner (oi.symm ⟨x, hxmem⟩))).property
        rw [Equiv.swap_apply_of_ne_of_ne
          (Finset.mem_erase.mp (Finset.mem_erase.mp hex).2).1 (Finset.mem_erase.mp hex).1]
        exact hextNe x hxmem

/-- `insertFirstPair` pairs position `0` with the chosen `j`. -/
@[simp]
theorem Pairing.insertFirstPair_partner_zero {n : ℕ} (pairing : Pairing n)
    (j : Fin (2 * (n + 1))) (hj : (0 : Fin (2 * (n + 1))) ≠ j) :
    (pairing.insertFirstPair j hj).partner 0 = j := by
  change (Equiv.swap 0 j *
    (pairing.partner.extendDomain (deletedPositionsOrderIso n j hj).toEquiv)) 0 = j
  rw [Equiv.Perm.mul_apply,
    Equiv.Perm.extendDomain_apply_not_subtype _ _ (by simp [deletedPositions]),
    Equiv.swap_apply_left]

/-- `insertFirstPair`'s chosen partner `j` pairs back with position `0`. -/
@[simp]
theorem Pairing.insertFirstPair_partner_chosen {n : ℕ} (pairing : Pairing n)
    (j : Fin (2 * (n + 1))) (hj : (0 : Fin (2 * (n + 1))) ≠ j) :
    (pairing.insertFirstPair j hj).partner j = 0 := by
  change (Equiv.swap 0 j *
    (pairing.partner.extendDomain (deletedPositionsOrderIso n j hj).toEquiv)) j = 0
  rw [Equiv.Perm.mul_apply,
    Equiv.Perm.extendDomain_apply_not_subtype _ _ (by simp [deletedPositions]),
    Equiv.swap_apply_right]

/-- On the positions left after removing `0` and `j`, `insertFirstPair`'s partner is exactly the
smaller pairing's own partner, transported across `deletedPositionsOrderIso`: this is the
conjugation formula `eraseZeroOrderIso_partner` needs a counterpart of on the insertion side. -/
@[simp]
theorem Pairing.insertFirstPair_partner_orderIso {n : ℕ} (pairing : Pairing n)
    (j : Fin (2 * (n + 1))) (hj : (0 : Fin (2 * (n + 1))) ≠ j) (i : Fin (2 * n)) :
    (pairing.insertFirstPair j hj).partner
        (deletedPositionsOrderIso n j hj i : Fin (2 * (n + 1))) =
      (deletedPositionsOrderIso n j hj (pairing.partner i) : Fin (2 * (n + 1))) := by
  set oi := deletedPositionsOrderIso n j hj
  change (Equiv.swap 0 j * (pairing.partner.extendDomain oi.toEquiv)) (oi i : Fin (2 * (n + 1))) =
    (oi (pairing.partner i) : Fin (2 * (n + 1)))
  rw [Equiv.Perm.mul_apply]
  have hmem : (oi i : Fin (2 * (n + 1))) ∈ deletedPositions n j hj := (oi i).property
  have h1 : pairing.partner.extendDomain oi.toEquiv (oi i : Fin (2 * (n + 1))) =
      (oi (pairing.partner (oi.symm ⟨(oi i : Fin (2 * (n + 1))), hmem⟩)) :
        Fin (2 * (n + 1))) :=
    Equiv.Perm.extendDomain_apply_subtype _ _ hmem
  rw [h1]
  have hsymm : oi.symm ⟨(oi i : Fin (2 * (n + 1))), hmem⟩ = i := by
    apply oi.injective
    simp
  rw [hsymm]
  have hmem' : (oi (pairing.partner i) : Fin (2 * (n + 1))) ∈ deletedPositions n j hj :=
    (oi (pairing.partner i)).property
  exact Equiv.swap_apply_of_ne_of_ne
    (Finset.mem_erase.mp (Finset.mem_erase.mp hmem').2).1 (Finset.mem_erase.mp hmem').1

/-- Inserting a new pair `(0, j)` ahead of `pairing`, then erasing the pair containing position
`0`, recovers `pairing` unchanged: `eraseZeroPair` is a left inverse of `insertFirstPair j hj`. -/
theorem Pairing.eraseZeroPair_insertFirstPair {n : ℕ} (pairing : Pairing n)
    (j : Fin (2 * (n + 1))) (hj : (0 : Fin (2 * (n + 1))) ≠ j) :
    (pairing.insertFirstPair j hj).eraseZeroPair = pairing := by
  set P := pairing.insertFirstPair j hj with hPdef
  have hPj : P.partner 0 = j := pairing.insertFirstPair_partner_zero j hj
  have hoi_eq : ∀ k : Fin (2 * n),
      (P.eraseZeroOrderIso k : Fin (2 * (n + 1))) =
        (deletedPositionsOrderIso n j hj k : Fin (2 * (n + 1))) :=
    deletedPositionsOrderIso_congr n hPj (Ne.symm (P.partner_ne 0)) hj
  apply Pairing.ext
  apply Equiv.ext
  intro i
  apply P.eraseZeroOrderIso.injective
  apply Subtype.ext
  rw [Pairing.eraseZeroOrderIso_partner, hoi_eq, hoi_eq]
  rw [hPdef, pairing.insertFirstPair_partner_orderIso j hj i]

/-- Erasing the pair containing position `0` from `pairing`, then reinserting a pair with the
same partner, recovers `pairing` unchanged: on the fiber of pairings with `partner 0 = j`,
`insertFirstPair j hj` is a left inverse of `eraseZeroPair`. -/
theorem Pairing.insertFirstPair_eraseZeroPair {n : ℕ} (pairing : Pairing (n + 1)) :
    pairing.eraseZeroPair.insertFirstPair (pairing.partner 0)
      (Ne.symm (pairing.partner_ne 0)) = pairing := by
  apply Pairing.ext
  apply Equiv.ext
  intro x
  by_cases hx0 : x = 0
  · subst hx0
    exact pairing.eraseZeroPair.insertFirstPair_partner_zero (pairing.partner 0)
      (Ne.symm (pairing.partner_ne 0))
  · by_cases hxj : x = pairing.partner 0
    · subst hxj
      rw [pairing.eraseZeroPair.insertFirstPair_partner_chosen (pairing.partner 0)
        (Ne.symm (pairing.partner_ne 0))]
      exact (pairing.partner_partner 0).symm
    · have hxmem : x ∈ deletedPositions n (pairing.partner 0) (Ne.symm (pairing.partner_ne 0)) := by
        simp [deletedPositions, hx0, hxj]
      set k := pairing.eraseZeroOrderIso.symm ⟨x, hxmem⟩ with hkdef
      have hxeq : (pairing.eraseZeroOrderIso k : Fin (2 * (n + 1))) = x := by simp [hkdef]
      have hkey := pairing.eraseZeroPair.insertFirstPair_partner_orderIso (pairing.partner 0)
        (Ne.symm (pairing.partner_ne 0)) k
      rw [← hxeq]
      exact hkey.trans (Pairing.eraseZeroOrderIso_partner pairing k)

/-- **A `Pairing (n + 1)` decomposes into a choice of position `0`'s partner together with the
smaller pairing left after removing it.** `eraseZeroPair_insertFirstPair` and
`insertFirstPair_eraseZeroPair` are exactly the two `Equiv.left_inv`/`right_inv` obligations this
needs: `eraseZeroPair` is not globally injective on `Pairing (n + 1)` (distinct choices of `0`'s
partner can erase to the same smaller pairing), so this is an equivalence with the fiber-indexed
sigma type, not a claim that `eraseZeroPair` alone is a global bijection. -/
noncomputable def Pairing.equivSigma (n : ℕ) :
    Pairing (n + 1) ≃ Σ _ : {j : Fin (2 * (n + 1)) // (0 : Fin (2 * (n + 1))) ≠ j}, Pairing n where
  toFun pairing := ⟨⟨pairing.partner 0, Ne.symm (pairing.partner_ne 0)⟩, pairing.eraseZeroPair⟩
  invFun jQ := jQ.2.insertFirstPair jQ.1.1 jQ.1.2
  left_inv pairing := pairing.insertFirstPair_eraseZeroPair
  right_inv jQ := by
    obtain ⟨⟨j, hj⟩, Q⟩ := jQ
    refine Sigma.ext (Subtype.ext ?_) ?_
    · exact Q.insertFirstPair_partner_zero j hj
    · exact heq_of_eq (Q.eraseZeroPair_insertFirstPair j hj)

/-- The adjacent four-position pairing `(0,1)(2,3)`. -/
def pairingAdjacent : Pairing 2 :=
  Pairing.ofPartner (Equiv.swap 0 1 * Equiv.swap 2 3) (by decide)

/-- The crossing four-position pairing `(0,2)(1,3)`. -/
def pairingCrossing : Pairing 2 :=
  Pairing.ofPartner (Equiv.swap 0 2 * Equiv.swap 1 3) (by decide)

/-- The nested four-position pairing `(0,3)(1,2)`. -/
def pairingNested : Pairing 2 :=
  Pairing.ofPartner (Equiv.swap 0 3 * Equiv.swap 1 2) (by decide)

/-- There are exactly three perfect pairings of four ordered positions, stated as a `Finset`
equality so the result is independent of any enumeration order. -/
theorem allPairings_two :
    allPairings 2 = {pairingAdjacent, pairingCrossing, pairingNested} := by
  decide

@[simp]
theorem crossingCount_pairingAdjacent : pairingAdjacent.crossingCount = 0 := by
  decide

@[simp]
theorem crossingCount_pairingCrossing : pairingCrossing.crossingCount = 1 := by
  decide

@[simp]
theorem crossingCount_pairingNested : pairingNested.crossingCount = 0 := by
  decide

end BlochDeDominicis
end Common
end SecondQuantization
