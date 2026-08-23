import LeanCondensedMatter.Combinatorics.PerfectPairing.CrossingParity

set_option linter.style.header false

/-!
# A perfect pairing as a permutation of its ambient positions

Listing the normalized pairs of a perfect pairing one after another turns the pairing into a
permutation of `Fin (2 * n)`: the block of positions `2 * k` and `2 * k + 1` receives the two
endpoints of the `k`-th pair, first endpoint first.

The enumeration of the pairs is arbitrary; nothing here depends on the choice.
-/

namespace Combinatorics

variable {n : ℕ}

/-- Split an ambient position into the index of its two-element block and the slot inside it. -/
def pairSlotIndexEquiv (n : ℕ) : Fin (2 * n) ≃ Fin n × Fin 2 :=
  (finCongr (by ring)).trans (finProdFinEquiv (m := n) (n := 2)).symm

/-- Recover an ambient position from its block index and its slot inside the block. -/
theorem pairSlotIndexEquiv_reconstruct_val (n : ℕ) (p : Fin (2 * n)) :
    p.val = (pairSlotIndexEquiv n p).2.val + 2 * (pairSlotIndexEquiv n p).1.val := by
  have h := congrArg (fun q => q.val) ((pairSlotIndexEquiv n).symm_apply_apply p)
  simpa [pairSlotIndexEquiv, finProdFinEquiv] using h.symm

/-- Ambient positions are ordered by block index first, and by slot inside the block second. -/
theorem pairSlotIndexEquiv_lt_iff (n : ℕ) (p q : Fin (2 * n)) :
    p < q ↔
      (pairSlotIndexEquiv n p).1 < (pairSlotIndexEquiv n q).1 ∨
        ((pairSlotIndexEquiv n p).1 = (pairSlotIndexEquiv n q).1 ∧
          (pairSlotIndexEquiv n p).2 < (pairSlotIndexEquiv n q).2) := by
  have hp := pairSlotIndexEquiv_reconstruct_val n p
  have hq := pairSlotIndexEquiv_reconstruct_val n q
  have hps := (pairSlotIndexEquiv n p).2.isLt
  have hqs := (pairSlotIndexEquiv n q).2.isLt
  constructor
  · intro h
    have hval : p.val < q.val := h
    rcases lt_trichotomy (pairSlotIndexEquiv n p).1 (pairSlotIndexEquiv n q).1 with hlt | heq | hgt
    · exact Or.inl hlt
    · refine Or.inr ⟨heq, ?_⟩
      have hk : (pairSlotIndexEquiv n p).1.val = (pairSlotIndexEquiv n q).1.val :=
        congrArg Fin.val heq
      change (pairSlotIndexEquiv n p).2.val < (pairSlotIndexEquiv n q).2.val
      omega
    · have hgt' : (pairSlotIndexEquiv n q).1.val < (pairSlotIndexEquiv n p).1.val := hgt
      omega
  · rintro (hlt | ⟨heq, hslot⟩)
    · have hlt' : (pairSlotIndexEquiv n p).1.val < (pairSlotIndexEquiv n q).1.val := hlt
      change p.val < q.val
      omega
    · have hk : (pairSlotIndexEquiv n p).1.val = (pairSlotIndexEquiv n q).1.val :=
        congrArg Fin.val heq
      have hs : (pairSlotIndexEquiv n p).2.val < (pairSlotIndexEquiv n q).2.val := hslot
      change p.val < q.val
      omega

/-- An enumeration of the normalized pairs of `pairing`. -/
noncomputable def Pairing.pairIndexEquiv (pairing : Pairing n) :
    Fin n ≃ pairing.NormalizedPair :=
  (Fintype.equivFinOfCardEq pairing.card_normalizedPair).symm

/-- Ambient positions viewed as an enumerated pair together with an endpoint selector. -/
noncomputable def Pairing.pairSlotEquiv (pairing : Pairing n) :
    Fin n × Fin 2 ≃ Fin (2 * n) :=
  (pairing.pairIndexEquiv.prodCongr (Equiv.refl (Fin 2))).trans pairing.pairEndpointEquiv

/-- Slot `0` of a block selects the first endpoint of its pair. -/
theorem Pairing.pairSlotEquiv_zero (pairing : Pairing n) (k : Fin n) :
    pairing.pairSlotEquiv (k, 0) = (pairing.pairIndexEquiv k).1.1 := by
  change pairing.pairEndpoint (pairing.pairIndexEquiv k, 0) = _
  simp

/-- Slot `1` of a block selects the second endpoint of its pair. -/
theorem Pairing.pairSlotEquiv_one (pairing : Pairing n) (k : Fin n) :
    pairing.pairSlotEquiv (k, 1) = (pairing.pairIndexEquiv k).1.2 := by
  change pairing.pairEndpoint (pairing.pairIndexEquiv k, 1) = _
  simp

/-- The two slots of a block are ordered, since the enumerated pairs are normalized. -/
theorem Pairing.pairSlotEquiv_zero_lt_one (pairing : Pairing n) (k : Fin n) :
    pairing.pairSlotEquiv (k, 0) < pairing.pairSlotEquiv (k, 1) := by
  rw [pairing.pairSlotEquiv_zero, pairing.pairSlotEquiv_one]
  exact pairing.pairs_normalized (pairing.pairIndexEquiv k).2

/-- The two slots of a block are partners: this is what makes the enumeration present the
pairing. -/
theorem Pairing.partner_pairSlotEquiv_zero (pairing : Pairing n) (k : Fin n) :
    pairing.partner (pairing.pairSlotEquiv (k, 0)) = pairing.pairSlotEquiv (k, 1) := by
  rw [pairing.pairSlotEquiv_zero, pairing.pairSlotEquiv_one]
  exact ((pairing.mem_pairs_iff _ _).1 (pairing.pairIndexEquiv k).2).2

/-- The permutation of ambient positions that lists the normalized pairs one after another. -/
noncomputable def Pairing.pairPerm (pairing : Pairing n) : Equiv.Perm (Fin (2 * n)) :=
  (pairSlotIndexEquiv n).trans pairing.pairSlotEquiv

theorem Pairing.pairPerm_apply (pairing : Pairing n) (p : Fin (2 * n)) :
    pairing.pairPerm p = pairing.pairSlotEquiv (pairSlotIndexEquiv n p) :=
  rfl

/-- On the position with block index `k` and slot `s`, the pair-listing permutation returns the
corresponding endpoint of the `k`-th pair. -/
@[simp]
theorem Pairing.pairPerm_pairSlotIndexEquiv_symm (pairing : Pairing n) (x : Fin n × Fin 2) :
    pairing.pairPerm ((pairSlotIndexEquiv n).symm x) = pairing.pairSlotEquiv x := by
  rw [Pairing.pairPerm_apply, Equiv.apply_symm_apply]

private theorem prod_Ioi_eq_prod_ite {M : Type*} [CommMonoid M] {m : ℕ}
    (i : Fin m) (g : Fin m → M) :
    (∏ j ∈ Finset.Ioi i, g j) = ∏ j : Fin m, if i < j then g j else 1 := by
  rw [← Finset.prod_filter]
  congr 1
  ext j
  simp

/-- The sign of a permutation of `Fin (2 * n)`, expanded over ordered pairs of positions indexed by
their two-element block and their slot inside it. -/
theorem sign_eq_prod_prod_blockSlots (σ : Equiv.Perm (Fin (2 * n))) :
    Equiv.Perm.sign σ =
      ∏ x : Fin n × Fin 2, ∏ y : Fin n × Fin 2,
        (if (pairSlotIndexEquiv n).symm x < (pairSlotIndexEquiv n).symm y then
            (if σ ((pairSlotIndexEquiv n).symm x) < σ ((pairSlotIndexEquiv n).symm y)
              then (1 : ℤˣ) else -1)
          else 1) := by
  classical
  calc
    Equiv.Perm.sign σ =
        ∏ i : Fin (2 * n), ∏ j ∈ Finset.Ioi i, (if σ i < σ j then (1 : ℤˣ) else -1) :=
      Equiv.Perm.sign_eq_prod_prod_Ioi σ
    _ = ∏ i : Fin (2 * n), ∏ j : Fin (2 * n),
          (if i < j then (if σ i < σ j then (1 : ℤˣ) else -1) else 1) :=
      Finset.prod_congr rfl fun i _ => prod_Ioi_eq_prod_ite i _
    _ = ∏ x : Fin n × Fin 2, ∏ j : Fin (2 * n),
          (if (pairSlotIndexEquiv n).symm x < j then
              (if σ ((pairSlotIndexEquiv n).symm x) < σ j then (1 : ℤˣ) else -1)
            else 1) :=
      (Equiv.prod_comp (pairSlotIndexEquiv n).symm _).symm
    _ = ∏ x : Fin n × Fin 2, ∏ y : Fin n × Fin 2,
          (if (pairSlotIndexEquiv n).symm x < (pairSlotIndexEquiv n).symm y then
              (if σ ((pairSlotIndexEquiv n).symm x) < σ ((pairSlotIndexEquiv n).symm y)
                then (1 : ℤˣ) else -1)
            else 1) :=
      Finset.prod_congr rfl fun x _ =>
        (Equiv.prod_comp (pairSlotIndexEquiv n).symm _).symm

/-- Positions compare through their block index first and their slot second. -/
theorem pairSlotIndexEquiv_symm_lt_iff (n : ℕ) (x y : Fin n × Fin 2) :
    (pairSlotIndexEquiv n).symm x < (pairSlotIndexEquiv n).symm y ↔
      x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2) := by
  rw [pairSlotIndexEquiv_lt_iff n]
  simp

private theorem neg_one_pow_eq_of_mod_two_eq {a b : ℕ} (h : a % 2 = b % 2) :
    (-1 : ℤˣ) ^ a = (-1) ^ b := by
  have hsq : (-1 : ℤˣ) * (-1) = 1 := by decide
  conv_lhs => rw [← Nat.div_add_mod a 2]
  conv_rhs => rw [← Nat.div_add_mod b 2, ← h]
  rw [pow_add, pow_add, pow_mul, pow_mul, sq, hsq, one_pow, one_pow]

private theorem ite_lt_eq_neg_one_pow {m : ℕ} (a b : Fin m) (hab : a ≠ b) :
    (if a < b then (1 : ℤˣ) else -1) = (-1) ^ (if b < a then 1 else 0) := by
  rcases lt_trichotomy a b with h | h | h
  · rw [if_pos h, if_neg (asymm h), pow_zero]
  · exact absurd h hab
  · rw [if_neg (asymm h), if_pos h, pow_one]

/-- The ambient position carried by the slot `x` of a permutation. -/
private def blockPos (τ : Equiv.Perm (Fin (2 * n))) (x : Fin n × Fin 2) : Fin (2 * n) :=
  τ ((pairSlotIndexEquiv n).symm x)

/-- The two ambient positions carried by the `k`-th two-element block, in slot order. -/
def blockPair (τ : Equiv.Perm (Fin (2 * n))) (k : Fin n) : Fin (2 * n) × Fin (2 * n) :=
  (blockPos τ (k, 0), blockPos τ (k, 1))

/-- The two positions of a block, written through the block-slot presentation. `blockPos` is an
implementation detail, so this is how a caller outside this module computes a `blockPair`. -/
theorem blockPair_apply (τ : Equiv.Perm (Fin (2 * n))) (k : Fin n) :
    blockPair τ k =
      (τ ((pairSlotIndexEquiv n).symm (k, 0)), τ ((pairSlotIndexEquiv n).symm (k, 1))) :=
  rfl

private theorem blockPos_ne (τ : Equiv.Perm (Fin (2 * n))) {x y : Fin n × Fin 2} (h : x ≠ y) :
    blockPos τ x ≠ blockPos τ y := fun heq =>
  h ((pairSlotIndexEquiv n).symm.injective (τ.injective heq))

/-- The sign contribution of the ordered pair of positions with block indices and slots `x` and
`y`. -/
private noncomputable def slotFactor (τ : Equiv.Perm (Fin (2 * n))) (x y : Fin n × Fin 2) : ℤˣ :=
  if (pairSlotIndexEquiv n).symm x < (pairSlotIndexEquiv n).symm y then
      (if blockPos τ x < blockPos τ y then (1 : ℤˣ) else -1)
    else 1

/-- The sign contribution of an ordered pair of two-element blocks. -/
private noncomputable def blockFactor (τ : Equiv.Perm (Fin (2 * n))) (k l : Fin n) : ℤˣ :=
  ∏ s : Fin 2, ∏ t : Fin 2, slotFactor τ (k, s) (l, t)

private theorem sign_eq_prod_blockFactor (τ : Equiv.Perm (Fin (2 * n))) :
    Equiv.Perm.sign τ = ∏ k : Fin n, ∏ l : Fin n, blockFactor τ k l := by
  classical
  have hslot : Equiv.Perm.sign τ =
      ∏ x : Fin n × Fin 2, ∏ y : Fin n × Fin 2, slotFactor τ x y :=
    sign_eq_prod_prod_blockSlots τ
  rw [hslot, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun k _ => ?_
  calc
    (∏ s : Fin 2, ∏ y : Fin n × Fin 2, slotFactor τ (k, s) y) =
        ∏ s : Fin 2, ∏ l : Fin n, ∏ t : Fin 2, slotFactor τ (k, s) (l, t) :=
      Finset.prod_congr rfl fun s _ => Fintype.prod_prod_type _
    _ = ∏ l : Fin n, ∏ s : Fin 2, ∏ t : Fin 2, slotFactor τ (k, s) (l, t) :=
      Finset.prod_comm
    _ = ∏ l : Fin n, blockFactor τ k l := rfl

private theorem blockFactor_of_gt (τ : Equiv.Perm (Fin (2 * n))) {k l : Fin n} (h : l < k) :
    blockFactor τ k l = 1 := by
  refine Finset.prod_eq_one fun s _ => Finset.prod_eq_one fun t _ => ?_
  rw [slotFactor]
  apply if_neg
  rw [pairSlotIndexEquiv_symm_lt_iff]
  rintro (hlt | ⟨heq, -⟩)
  · exact absurd hlt (asymm h)
  · exact absurd heq (Ne.symm (ne_of_lt h))

private theorem blockFactor_self (τ : Equiv.Perm (Fin (2 * n))) (k : Fin n) :
    blockFactor τ k k =
      (-1) ^ (if (blockPair τ k).2 < (blockPair τ k).1 then 1 else 0) := by
  have hnotlt : ∀ s t : Fin 2, ¬ (s < t) →
      ¬ ((pairSlotIndexEquiv n).symm (k, s) < (pairSlotIndexEquiv n).symm (k, t)) := by
    intro s t hst hlt
    rcases (pairSlotIndexEquiv_symm_lt_iff n (k, s) (k, t)).1 hlt with h | ⟨-, h⟩
    · exact absurd h (lt_irrefl k)
    · exact hst h
  have hlt01 : (pairSlotIndexEquiv n).symm (k, 0) < (pairSlotIndexEquiv n).symm (k, 1) :=
    (pairSlotIndexEquiv_symm_lt_iff n (k, 0) (k, 1)).2
      (Or.inr ⟨rfl, (by decide : (0 : Fin 2) < 1)⟩)
  have hne : blockPos τ (k, 0) ≠ blockPos τ (k, 1) := by
    refine blockPos_ne τ ?_
    intro hxy
    have hslot : (0 : Fin 2) = 1 := congrArg Prod.snd hxy
    exact absurd hslot (by decide)
  rw [blockFactor]
  simp only [Fin.prod_univ_two, slotFactor]
  rw [if_neg (hnotlt 0 0 (by decide)), if_pos hlt01,
    if_neg (hnotlt 1 0 (by decide)), if_neg (hnotlt 1 1 (by decide)),
    ite_lt_eq_neg_one_pow _ _ hne]
  simp only [one_mul, mul_one, blockPair]

private theorem blockFactor_of_lt (τ : Equiv.Perm (Fin (2 * n))) {k l : Fin n} (h : k < l) :
    blockFactor τ k l =
      (-1) ^ pairEndpointInversionCount (blockPair τ k) (blockPair τ l) := by
  have hpos : ∀ s t : Fin 2,
      (pairSlotIndexEquiv n).symm (k, s) < (pairSlotIndexEquiv n).symm (l, t) :=
    fun s t => (pairSlotIndexEquiv_symm_lt_iff n (k, s) (l, t)).2 (Or.inl h)
  have hne : ∀ s t : Fin 2, blockPos τ (k, s) ≠ blockPos τ (l, t) := by
    intro s t
    refine blockPos_ne τ ?_
    intro hxy
    exact absurd (congrArg Prod.fst hxy) (ne_of_lt h)
  rw [blockFactor]
  simp only [Fin.prod_univ_two, slotFactor]
  rw [if_pos (hpos 0 0), if_pos (hpos 0 1), if_pos (hpos 1 0), if_pos (hpos 1 1),
    ite_lt_eq_neg_one_pow _ _ (hne 0 0),
    ite_lt_eq_neg_one_pow _ _ (hne 0 1),
    ite_lt_eq_neg_one_pow _ _ (hne 1 0),
    ite_lt_eq_neg_one_pow _ _ (hne 1 1),
    ← pow_add, ← pow_add, ← pow_add]
  congr 1
  simp only [pairEndpointInversionCount, blockPair]
  ac_rfl

/-- **Block form of a permutation sign.** Grouping the ambient positions into two-element blocks,
the sign of any permutation is `-1` raised to the number of blocks it reverses plus the endpoint
inversions between distinct blocks. -/
theorem sign_eq_pow_blockInversions (τ : Equiv.Perm (Fin (2 * n))) :
    Equiv.Perm.sign τ =
      (-1) ^ (∑ k : Fin n, if (blockPair τ k).2 < (blockPair τ k).1 then 1 else 0) *
        (-1) ^ (∑ k : Fin n, ∑ l ∈ Finset.Ioi k,
          pairEndpointInversionCount (blockPair τ k) (blockPair τ l)) := by
  classical
  rw [sign_eq_prod_blockFactor]
  have hsplit : ∀ k : Fin n,
      (∏ l : Fin n, blockFactor τ k l) =
        blockFactor τ k k * ∏ l ∈ Finset.Ioi k, blockFactor τ k l := by
    intro k
    have hIci : (∏ l ∈ Finset.Ici k, blockFactor τ k l) = ∏ l : Fin n, blockFactor τ k l := by
      refine Finset.prod_subset (Finset.subset_univ _) ?_
      intro l _ hl
      refine blockFactor_of_gt τ ?_
      simpa [Finset.mem_Ici, not_le] using hl
    rw [← hIci, ← Finset.Ioi_insert, Finset.prod_insert (by simp)]
  calc
    (∏ k : Fin n, ∏ l : Fin n, blockFactor τ k l) =
        ∏ k : Fin n, (blockFactor τ k k * ∏ l ∈ Finset.Ioi k, blockFactor τ k l) :=
      Finset.prod_congr rfl fun k _ => hsplit k
    _ = (∏ k : Fin n, blockFactor τ k k) *
          ∏ k : Fin n, ∏ l ∈ Finset.Ioi k, blockFactor τ k l :=
      Finset.prod_mul_distrib
    _ = (∏ k : Fin n, (-1 : ℤˣ) ^
            (if (blockPair τ k).2 < (blockPair τ k).1 then 1 else 0)) *
          ∏ k : Fin n, ∏ l ∈ Finset.Ioi k,
            (-1 : ℤˣ) ^ pairEndpointInversionCount (blockPair τ k) (blockPair τ l) := by
      refine congrArg₂ (· * ·) ?_ ?_
      · exact Finset.prod_congr rfl fun k _ => blockFactor_self τ k
      · exact Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun l hl =>
          blockFactor_of_lt τ (Finset.mem_Ioi.1 hl)
    _ = (-1 : ℤˣ) ^ (∑ k : Fin n, if (blockPair τ k).2 < (blockPair τ k).1 then 1 else 0) *
          (-1 : ℤˣ) ^ (∑ k : Fin n, ∑ l ∈ Finset.Ioi k,
            pairEndpointInversionCount (blockPair τ k) (blockPair τ l)) := by
      refine congrArg₂ (· * ·) (Finset.prod_pow_eq_pow_sum _ _ _) ?_
      rw [← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_congr rfl fun k _ => Finset.prod_pow_eq_pow_sum _ _ _

private theorem blockPair_pairPerm (pairing : Pairing n) (k : Fin n) :
    blockPair pairing.pairPerm k = (pairing.pairIndexEquiv k).1 := by
  rw [blockPair, blockPos, blockPos, Pairing.pairPerm_pairSlotIndexEquiv_symm,
    Pairing.pairPerm_pairSlotIndexEquiv_symm, pairing.pairSlotEquiv_zero,
    pairing.pairSlotEquiv_one]

private theorem sum_univ_eq_sum_Ioi_add_sum_Iio {m : ℕ} (k : Fin m) (f : Fin m → ℕ)
    (hk : f k = 0) :
    ∑ l : Fin m, f l = ∑ l ∈ Finset.Ioi k, f l + ∑ l ∈ Finset.Iio k, f l := by
  classical
  have hsplit :
      (∑ l ∈ Finset.univ.filter (fun l => l < k), f l) +
          ∑ l ∈ Finset.univ.filter (fun l => ¬ l < k), f l =
        ∑ l : Fin m, f l :=
    Finset.sum_filter_add_sum_filter_not Finset.univ (fun l => l < k) f
  have hIio : Finset.univ.filter (fun l => l < k) = Finset.Iio k := by
    ext l
    simp
  have hIci : Finset.univ.filter (fun l => ¬ l < k) = Finset.Ici k := by
    ext l
    simp [not_lt]
  have hIci_sum : ∑ l ∈ Finset.Ici k, f l = ∑ l ∈ Finset.Ioi k, f l := by
    rw [← Finset.Ioi_insert, Finset.sum_insert (by simp), hk, zero_add]
  rw [hIio, hIci, hIci_sum] at hsplit
  omega

/-- Indicator of a crossing between the pairs an equivalence assigns to `k` and `l`. -/
private noncomputable def crossIndicator (pairing : Pairing n) (e : Fin n ≃ pairing.NormalizedPair)
    (k l : Fin n) : ℕ :=
  if Crosses (e k).1 (e l).1 then 1 else 0

private theorem crossingCount_eq_sum_sum_crossIndicator (pairing : Pairing n)
    (e : Fin n ≃ pairing.NormalizedPair) :
    pairing.crossingCount = ∑ k : Fin n, ∑ l : Fin n, crossIndicator pairing e k l := by
  rw [pairing.crossingCount_eq_sum_sum_crosses, ← Equiv.sum_comp e]
  exact Finset.sum_congr rfl fun k _ => (Equiv.sum_comp e _).symm

private theorem crossingCount_eq_sum_Ioi_crossIndicator (pairing : Pairing n)
    (e : Fin n ≃ pairing.NormalizedPair) :
    pairing.crossingCount =
      ∑ k : Fin n, ∑ l ∈ Finset.Ioi k,
        (crossIndicator pairing e k l + crossIndicator pairing e l k) := by
  classical
  have hdiag : ∀ k : Fin n, crossIndicator pairing e k k = 0 :=
    fun k => if_neg (not_crosses_self _)
  have hswap :
      (∑ k : Fin n, ∑ l ∈ Finset.Iio k, crossIndicator pairing e k l) =
        ∑ k : Fin n, ∑ l ∈ Finset.Ioi k, crossIndicator pairing e l k :=
    Finset.sum_comm' (fun x y => by simp)
  rw [crossingCount_eq_sum_sum_crossIndicator pairing e]
  calc
    (∑ k : Fin n, ∑ l : Fin n, crossIndicator pairing e k l) =
        ∑ k : Fin n, (∑ l ∈ Finset.Ioi k, crossIndicator pairing e k l +
          ∑ l ∈ Finset.Iio k, crossIndicator pairing e k l) :=
      Finset.sum_congr rfl fun k _ =>
        sum_univ_eq_sum_Ioi_add_sum_Iio k (crossIndicator pairing e k) (hdiag k)
    _ = (∑ k : Fin n, ∑ l ∈ Finset.Ioi k, crossIndicator pairing e k l) +
          ∑ k : Fin n, ∑ l ∈ Finset.Iio k, crossIndicator pairing e k l :=
      Finset.sum_add_distrib
    _ = (∑ k : Fin n, ∑ l ∈ Finset.Ioi k, crossIndicator pairing e k l) +
          ∑ k : Fin n, ∑ l ∈ Finset.Ioi k, crossIndicator pairing e l k := by
      rw [hswap]
    _ = ∑ k : Fin n, ∑ l ∈ Finset.Ioi k,
          (crossIndicator pairing e k l + crossIndicator pairing e l k) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_add_distrib.symm

private theorem sum_Ioi_pairEndpointInversionCount_mod_two_eq_crossingCount (pairing : Pairing n)
    (e : Fin n ≃ pairing.NormalizedPair) :
    (∑ k : Fin n, ∑ l ∈ Finset.Ioi k, pairEndpointInversionCount (e k).1 (e l).1) % 2 =
      pairing.crossingCount % 2 := by
  classical
  rw [crossingCount_eq_sum_Ioi_crossIndicator pairing e]
  refine finset_sum_mod_two_congr _ _ _ fun k _ => ?_
  refine finset_sum_mod_two_congr _ _ _ fun l hl => ?_
  have hkl : k < l := Finset.mem_Ioi.1 hl
  have hne : e k ≠ e l := fun h => (ne_of_lt hkl) (e.injective h)
  have hEnds := pairing.normalizedPair_endpoints_ne_of_ne _ _ hne
  have hmod := pairEndpointInversionCount_mod_two_eq_crossesIndicator
    (e k).1 (e l).1
    (pairing.pairs_normalized (e k).2) (pairing.pairs_normalized (e l).2)
    hEnds.1 hEnds.2.1 hEnds.2.2.1 hEnds.2.2.2
  rw [hmod, crossIndicator, crossIndicator]
  by_cases hA : Crosses (e k).1 (e l).1
  · have hB : ¬ Crosses (e l).1 (e k).1 := fun h => lt_asymm hA.1 h.1
    simp [hA, hB]
  · by_cases hB : Crosses (e l).1 (e k).1 <;> simp [hA, hB]

/-- Swapping the endpoints of the first pair leaves the endpoint inversion count unchanged: the
same four comparisons occur, only reordered. -/
private theorem pairEndpointInversionCount_swap_left {n : ℕ}
    (left right : Fin (2 * n) × Fin (2 * n)) :
    pairEndpointInversionCount left.swap right = pairEndpointInversionCount left right := by
  simp only [pairEndpointInversionCount, Prod.swap]
  ac_rfl

/-- Swapping the endpoints of the second pair leaves the endpoint inversion count unchanged. -/
private theorem pairEndpointInversionCount_swap_right {n : ℕ}
    (left right : Fin (2 * n) × Fin (2 * n)) :
    pairEndpointInversionCount left right.swap = pairEndpointInversionCount left right := by
  simp only [pairEndpointInversionCount, Prod.swap]
  ac_rfl

/-- A permutation of ambient positions **presents** a pairing when its two-element blocks are
exactly the normalized pairs of `pairing`, each in either endpoint order. -/
def Pairing.PresentsPairs (pairing : Pairing n) (τ : Equiv.Perm (Fin (2 * n))) : Prop :=
  ∃ e : Fin n ≃ pairing.NormalizedPair, ∀ k : Fin n,
    blockPair τ k = (e k).1 ∨ blockPair τ k = (e k).1.swap

private theorem pairEndpointInversionCount_blockPair_eq {pairing : Pairing n}
    {τ : Equiv.Perm (Fin (2 * n))} {e : Fin n ≃ pairing.NormalizedPair}
    (hpres : ∀ k : Fin n, blockPair τ k = (e k).1 ∨ blockPair τ k = (e k).1.swap)
    (k l : Fin n) :
    pairEndpointInversionCount (blockPair τ k) (blockPair τ l) =
      pairEndpointInversionCount (e k).1 (e l).1 := by
  rcases hpres k with hk | hk <;> rcases hpres l with hl | hl <;>
    simp [hk, hl, pairEndpointInversionCount_swap_left, pairEndpointInversionCount_swap_right]

/-- **Sign under presentation.** If a permutation's two-element blocks carry the normalized pairs of
`pairing`, each in either endpoint order, its sign is `-1` to the number of reversed blocks times
`-1` to `pairing`'s crossing count. -/
theorem Pairing.sign_eq_of_presentsPairs (pairing : Pairing n) (τ : Equiv.Perm (Fin (2 * n)))
    (h : pairing.PresentsPairs τ) :
    Equiv.Perm.sign τ =
      (-1) ^ (∑ k : Fin n, if (blockPair τ k).2 < (blockPair τ k).1 then 1 else 0) *
        (-1) ^ pairing.crossingCount := by
  classical
  obtain ⟨e, hpres⟩ := h
  rw [sign_eq_pow_blockInversions τ]
  congr 1
  refine neg_one_pow_eq_of_mod_two_eq ?_
  have heq : (∑ k : Fin n, ∑ l ∈ Finset.Ioi k,
      pairEndpointInversionCount (blockPair τ k) (blockPair τ l)) =
        ∑ k : Fin n, ∑ l ∈ Finset.Ioi k, pairEndpointInversionCount (e k).1 (e l).1 :=
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ =>
      pairEndpointInversionCount_blockPair_eq hpres k l
  rw [heq]
  exact sum_Ioi_pairEndpointInversionCount_mod_two_eq_crossingCount pairing e

/-- The pair-listing permutation presents its own pairing, with every block already in order. -/
theorem Pairing.pairPerm_presentsPairs (pairing : Pairing n) :
    pairing.PresentsPairs pairing.pairPerm :=
  ⟨pairing.pairIndexEquiv, fun k => Or.inl (blockPair_pairPerm pairing k)⟩

/-- **Criterion for presenting a pairing.** A permutation presents a pairing as soon as each of its
two-element blocks carries a pair of partners. No enumeration has to be supplied: the blocks are
disjoint and there are as many of them as there are pairs, so they exhaust the pairs. -/
theorem Pairing.presentsPairs_of_partner_blockPair (pairing : Pairing n)
    (τ : Equiv.Perm (Fin (2 * n)))
    (h : ∀ k : Fin n, pairing.partner (blockPair τ k).1 = (blockPair τ k).2) :
    pairing.PresentsPairs τ := by
  classical
  have hne : ∀ k : Fin n, (blockPair τ k).1 ≠ (blockPair τ k).2 := by
    intro k heq
    have := h k
    rw [← heq] at this
    exact absurd this (pairing.partner_ne _)
  have hmem : ∀ k : Fin n,
      (if (blockPair τ k).1 < (blockPair τ k).2 then blockPair τ k else (blockPair τ k).swap) ∈
        pairing.pairs := by
    intro k
    rcases lt_trichotomy (blockPair τ k).1 (blockPair τ k).2 with hlt | heq | hgt
    · rw [if_pos hlt]
      exact (pairing.mem_pairs_iff _ _).2 ⟨hlt, h k⟩
    · exact absurd heq (hne k)
    · rw [if_neg (asymm hgt)]
      refine (pairing.mem_pairs_iff _ _).2 ⟨hgt, ?_⟩
      rw [← h k, pairing.partner_partner]
  set f : Fin n → pairing.NormalizedPair := fun k => ⟨_, hmem k⟩ with hf
  have hfirst : ∀ k : Fin n,
      (f k).1 = blockPair τ k ∨ (f k).1 = (blockPair τ k).swap := by
    intro k
    by_cases hlt : (blockPair τ k).1 < (blockPair τ k).2
    · exact Or.inl (by simp [hf, hlt])
    · exact Or.inr (by simp [hf, hlt])
  have hblockPos_inj : ∀ x y : Fin n × Fin 2, blockPos τ x = blockPos τ y → x = y := by
    intro x y hxy
    by_contra hxy'
    exact blockPos_ne τ hxy' hxy
  have hinj : Function.Injective f := by
    intro k l hkl
    have hpair : (f k).1 = (f l).1 := congrArg Subtype.val hkl
    have hcoord : ∃ s : Fin 2, blockPos τ (k, 0) = blockPos τ (l, s) := by
      rcases hfirst k with hk | hk <;> rcases hfirst l with hl | hl <;>
        rw [hk, hl] at hpair
      · exact ⟨0, congrArg Prod.fst hpair⟩
      · exact ⟨1, congrArg Prod.fst hpair⟩
      · exact ⟨1, congrArg Prod.snd hpair⟩
      · exact ⟨0, congrArg Prod.snd hpair⟩
    obtain ⟨s, hs⟩ := hcoord
    exact congrArg Prod.fst (hblockPos_inj _ _ hs)
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2
      ⟨hinj, by simp [pairing.card_normalizedPair]⟩
  refine ⟨Equiv.ofBijective f hbij, fun k => ?_⟩
  have hEk : ((Equiv.ofBijective f hbij) k : Fin (2 * n) × Fin (2 * n)) =
      ((f k : pairing.NormalizedPair) : Fin (2 * n) × Fin (2 * n)) := rfl
  rw [hEk]
  rcases hfirst k with hk | hk
  · exact Or.inl hk.symm
  · exact Or.inr (by rw [hk, Prod.swap_swap])

/-- **Crossing parity is a permutation sign.** The sign of the permutation listing the normalized
pairs of a perfect pairing is `-1` raised to its crossing count. -/
theorem Pairing.sign_pairPerm (pairing : Pairing n) :
    Equiv.Perm.sign pairing.pairPerm = (-1) ^ pairing.crossingCount := by
  have hzero : (∑ k : Fin n,
      if (blockPair pairing.pairPerm k).2 < (blockPair pairing.pairPerm k).1 then 1 else 0) = 0 :=
    Finset.sum_eq_zero fun k _ => if_neg (by
      rw [blockPair_pairPerm]
      exact asymm (pairing.pairs_normalized (pairing.pairIndexEquiv k).2))
  rw [pairing.sign_eq_of_presentsPairs pairing.pairPerm pairing.pairPerm_presentsPairs, hzero,
    pow_zero, one_mul]

/-- **Transporting a sum permutation through a two-part presentation.** A permutation acting
independently on the two parts contributes the product of its two signs; everything that depends on
how the parts are interleaved is collected in the presentation-only permutation `u.trans v`.

This is the algebraic half of a component factorization: the interleaving sign is separated from the
component signs, and is then shown to be trivial by a block argument. -/
theorem sign_trans_sumCongr_trans {α β γ : Type*} [DecidableEq α] [Fintype α]
    [DecidableEq β] [Fintype β] [DecidableEq γ] [Fintype γ]
    (u : α ≃ β ⊕ γ) (v : β ⊕ γ ≃ α) (σ : Equiv.Perm β) (ρ : Equiv.Perm γ) :
    Equiv.Perm.sign (u.trans ((Equiv.sumCongr σ ρ).trans v)) =
      Equiv.Perm.sign (u.trans v) * (Equiv.Perm.sign σ * Equiv.Perm.sign ρ) := by
  have hsplit : u.trans ((Equiv.sumCongr σ ρ).trans v) =
      (u.trans ((Equiv.sumCongr σ ρ).trans u.symm)).trans (u.trans v) := by
    apply Equiv.ext
    intro x
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
  have htransported :
      Equiv.Perm.sign (u.trans ((Equiv.sumCongr σ ρ).trans u.symm)) =
        Equiv.Perm.sign (Equiv.sumCongr σ ρ) :=
    (Equiv.Perm.sign_eq_sign_of_equiv (Equiv.sumCongr σ ρ)
      (u.trans ((Equiv.sumCongr σ ρ).trans u.symm)) u.symm (fun _ => by simp)).symm
  rw [hsplit, Equiv.Perm.sign_trans, htransported, Equiv.Perm.sign_sumCongr, mul_comm]

end Combinatorics
