import LeanCondensedMatter.Combinatorics.PerfectPairing.PairEndpoints

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

end Combinatorics
