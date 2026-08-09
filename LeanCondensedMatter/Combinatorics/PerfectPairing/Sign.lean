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

/-- Recover an ambient position from its block index and its slot inside that block. -/
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

/-- The sign contribution of the ordered pair of positions with block indices and slots `x` and
`y`. -/
private noncomputable def slotFactor (pairing : Pairing n) (x y : Fin n × Fin 2) : ℤˣ :=
  if (pairSlotIndexEquiv n).symm x < (pairSlotIndexEquiv n).symm y then
      (if pairing.pairSlotEquiv x < pairing.pairSlotEquiv y then (1 : ℤˣ) else -1)
    else 1

/-- The sign contribution of an ordered pair of two-element blocks. -/
private noncomputable def blockFactor (pairing : Pairing n) (k l : Fin n) : ℤˣ :=
  ∏ s : Fin 2, ∏ t : Fin 2, slotFactor pairing (k, s) (l, t)

private theorem sign_pairPerm_eq_prod_blockFactor (pairing : Pairing n) :
    Equiv.Perm.sign pairing.pairPerm =
      ∏ k : Fin n, ∏ l : Fin n, blockFactor pairing k l := by
  classical
  have hslot : Equiv.Perm.sign pairing.pairPerm =
      ∏ x : Fin n × Fin 2, ∏ y : Fin n × Fin 2, slotFactor pairing x y := by
    rw [sign_eq_prod_prod_blockSlots]
    refine Finset.prod_congr rfl fun x _ => Finset.prod_congr rfl fun y _ => ?_
    rw [slotFactor, Pairing.pairPerm_pairSlotIndexEquiv_symm,
      Pairing.pairPerm_pairSlotIndexEquiv_symm]
  rw [hslot, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun k _ => ?_
  calc
    (∏ s : Fin 2, ∏ y : Fin n × Fin 2, slotFactor pairing (k, s) y) =
        ∏ s : Fin 2, ∏ l : Fin n, ∏ t : Fin 2, slotFactor pairing (k, s) (l, t) :=
      Finset.prod_congr rfl fun s _ => Fintype.prod_prod_type _
    _ = ∏ l : Fin n, ∏ s : Fin 2, ∏ t : Fin 2, slotFactor pairing (k, s) (l, t) :=
      Finset.prod_comm
    _ = ∏ l : Fin n, blockFactor pairing k l := rfl

private theorem blockFactor_of_gt (pairing : Pairing n) {k l : Fin n} (h : l < k) :
    blockFactor pairing k l = 1 := by
  refine Finset.prod_eq_one fun s _ => Finset.prod_eq_one fun t _ => ?_
  rw [slotFactor]
  apply if_neg
  rw [pairSlotIndexEquiv_symm_lt_iff]
  rintro (hlt | ⟨heq, -⟩)
  · exact absurd hlt (asymm h)
  · exact absurd heq (Ne.symm (ne_of_lt h))

private theorem blockFactor_self (pairing : Pairing n) (k : Fin n) :
    blockFactor pairing k k = 1 := by
  have hnotlt : ∀ s t : Fin 2, ¬ (s < t) →
      ¬ ((pairSlotIndexEquiv n).symm (k, s) < (pairSlotIndexEquiv n).symm (k, t)) := by
    intro s t hst hlt
    rcases (pairSlotIndexEquiv_symm_lt_iff n (k, s) (k, t)).1 hlt with h | ⟨-, h⟩
    · exact absurd h (lt_irrefl k)
    · exact hst h
  have hlt01 : (pairSlotIndexEquiv n).symm (k, 0) < (pairSlotIndexEquiv n).symm (k, 1) :=
    (pairSlotIndexEquiv_symm_lt_iff n (k, 0) (k, 1)).2
      (Or.inr ⟨rfl, (by decide : (0 : Fin 2) < 1)⟩)
  rw [blockFactor]
  simp only [Fin.prod_univ_two, slotFactor]
  rw [if_neg (hnotlt 0 0 (by decide)), if_pos hlt01,
    if_neg (hnotlt 1 0 (by decide)), if_neg (hnotlt 1 1 (by decide)),
    if_pos (pairing.pairSlotEquiv_zero_lt_one k)]
  simp

private theorem Pairing.pairSlotEquiv_ne (pairing : Pairing n) {k l : Fin n} (h : k ≠ l)
    (s t : Fin 2) :
    pairing.pairSlotEquiv (k, s) ≠ pairing.pairSlotEquiv (l, t) := by
  intro heq
  exact h (congrArg Prod.fst (pairing.pairSlotEquiv.injective heq))

private theorem blockFactor_of_lt (pairing : Pairing n) {k l : Fin n} (h : k < l) :
    blockFactor pairing k l =
      (-1) ^ pairEndpointInversionCount (pairing.pairIndexEquiv k).1
        (pairing.pairIndexEquiv l).1 := by
  have hpos : ∀ s t : Fin 2,
      (pairSlotIndexEquiv n).symm (k, s) < (pairSlotIndexEquiv n).symm (l, t) :=
    fun s t => (pairSlotIndexEquiv_symm_lt_iff n (k, s) (l, t)).2 (Or.inl h)
  rw [blockFactor]
  simp only [Fin.prod_univ_two, slotFactor]
  rw [if_pos (hpos 0 0), if_pos (hpos 0 1), if_pos (hpos 1 0), if_pos (hpos 1 1),
    ite_lt_eq_neg_one_pow _ _ (pairing.pairSlotEquiv_ne (ne_of_lt h) 0 0),
    ite_lt_eq_neg_one_pow _ _ (pairing.pairSlotEquiv_ne (ne_of_lt h) 0 1),
    ite_lt_eq_neg_one_pow _ _ (pairing.pairSlotEquiv_ne (ne_of_lt h) 1 0),
    ite_lt_eq_neg_one_pow _ _ (pairing.pairSlotEquiv_ne (ne_of_lt h) 1 1),
    ← pow_add, ← pow_add, ← pow_add]
  congr 1
  simp only [pairEndpointInversionCount, Pairing.pairSlotEquiv_zero, Pairing.pairSlotEquiv_one]
  ring

/-- The sign of the pair-listing permutation is `-1` raised to the total number of endpoint
inversions between distinct normalized pairs. -/
theorem Pairing.sign_pairPerm_eq_pow_inversionSum (pairing : Pairing n) :
    Equiv.Perm.sign pairing.pairPerm =
      (-1) ^ (∑ k : Fin n, ∑ l ∈ Finset.Ioi k,
        pairEndpointInversionCount (pairing.pairIndexEquiv k).1
          (pairing.pairIndexEquiv l).1) := by
  classical
  rw [sign_pairPerm_eq_prod_blockFactor]
  calc
    (∏ k : Fin n, ∏ l : Fin n, blockFactor pairing k l) =
        ∏ k : Fin n, ∏ l ∈ Finset.Ioi k, blockFactor pairing k l := by
      refine Finset.prod_congr rfl fun k _ => ?_
      refine (Finset.prod_subset (Finset.subset_univ _) ?_).symm
      intro l _ hl
      rcases lt_trichotomy k l with hkl | hkl | hkl
      · exact absurd (Finset.mem_Ioi.2 hkl) hl
      · subst hkl
        exact blockFactor_self pairing k
      · exact blockFactor_of_gt pairing hkl
    _ = ∏ k : Fin n, ∏ l ∈ Finset.Ioi k,
          (-1 : ℤˣ) ^ pairEndpointInversionCount (pairing.pairIndexEquiv k).1
            (pairing.pairIndexEquiv l).1 :=
      Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun l hl =>
        blockFactor_of_lt pairing (Finset.mem_Ioi.1 hl)
    _ = ∏ k : Fin n, (-1 : ℤˣ) ^ (∑ l ∈ Finset.Ioi k,
          pairEndpointInversionCount (pairing.pairIndexEquiv k).1
            (pairing.pairIndexEquiv l).1) :=
      Finset.prod_congr rfl fun k _ => Finset.prod_pow_eq_pow_sum _ _ _
    _ = (-1 : ℤˣ) ^ (∑ k : Fin n, ∑ l ∈ Finset.Ioi k,
          pairEndpointInversionCount (pairing.pairIndexEquiv k).1
            (pairing.pairIndexEquiv l).1) :=
      Finset.prod_pow_eq_pow_sum _ _ _

end Combinatorics
