import LeanCondensedMatter.Combinatorics.ExchangeSign
import LeanCondensedMatter.Permutation.ConnectedDecomposition
import LeanCondensedMatter.Combinatorics.PerfectPairing.Bipartite
import LeanCondensedMatter.Combinatorics.PerfectPairing.Evaluation
import LeanCondensedMatter.Combinatorics.PerfectPairing.Sign
import Mathlib.Data.Matrix.Basic

set_option linter.style.header false

/-!
# Exchange-weighted pairing to permutation reduction

This module owns the crossing-weighted perfect-pairing sum and the parity-sensitive bridge into the
generic permutation backend. The permutation sum itself is owned by
`Permutation.ConnectedDecomposition`, where arbitrary-`ζ` cycle weights factor over orbit blocks and
feed the generic cumulant machinery.

Only the pairing-to-permutation bridge is parity-sensitive and assumes `ζ * ζ = 1`. Determinant and
permanent are deliberately not owned here; consumers that need those standard matrix invariants may
specialize the generic permutation sum locally.

The public surface owned here is intentionally small:

* `pairingSum ζ` — the crossing-weighted sum over perfect pairings;
* `exchangeMatrix ζ` — the side-oriented pair-value matrix;
* `sideSplittingWeight ζ` — the global factor fixed by the chosen side splitting;
* `pairingSum_eq_permutationSum_of_inl_vanishing` — the one pairing-to-permutation reduction.

All pairing construction, listing, sign transport, selection-rule, and orientation-count machinery
is private implementation detail.
-/

namespace Combinatorics

variable {m n : ℕ}

/-- The exchange-weighted sum over all perfect pairings. -/
noncomputable def pairingSum {R : Type*} [CommSemiring R] (ζ : R)
    (pv : Fin (2 * n) → Fin (2 * n) → R) : R :=
  ∑ P : Pairing n, P.evaluation (ζ ^ P.crossingCount) pv

/-- Interpret an integer unit `±1` as the corresponding parity exchange weight `1` or `ζ`.
This is private because sign transport is only an implementation device for the pairing bridge. -/
private noncomputable def exchangeUnitWeight {R : Type*} [CommSemiring R] (ζ : R) (u : ℤˣ) : R :=
  if u = 1 then 1 else ζ

private theorem exchangeUnitWeight_mul {R : Type*} [CommSemiring R] (ζ : R) (hζ : ζ * ζ = 1)
    (u v : ℤˣ) :
    exchangeUnitWeight ζ (u * v) = exchangeUnitWeight ζ u * exchangeUnitWeight ζ v := by
  rcases Int.units_eq_one_or u with rfl | rfl <;>
    rcases Int.units_eq_one_or v with rfl | rfl <;>
    simp [exchangeUnitWeight, hζ]

private noncomputable def exchangeUnitWeightHom {R : Type*} [CommSemiring R]
    (ζ : R) (hζ : ζ * ζ = 1) : ℤˣ →* R where
  toFun := exchangeUnitWeight ζ
  map_one' := by simp [exchangeUnitWeight]
  map_mul' := exchangeUnitWeight_mul ζ hζ

private theorem exchangeUnitWeight_neg_one_pow {R : Type*} [CommSemiring R]
    (ζ : R) (hζ : ζ * ζ = 1) (k : ℕ) :
    exchangeUnitWeight ζ ((-1 : ℤˣ) ^ k) = ζ ^ k := by
  change exchangeUnitWeightHom ζ hζ ((-1 : ℤˣ) ^ k) = ζ ^ k
  rw [map_pow]
  simp [exchangeUnitWeightHom, exchangeUnitWeight]

private theorem cycleType_card_le_sum {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) : σ.cycleType.card ≤ σ.cycleType.sum := by
  have h : ∀ s : Multiset ℕ, (∀ a ∈ s, 1 ≤ a) → s.card ≤ s.sum := by
    intro s hs
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons a s ih =>
        have ha : 1 ≤ a := hs a (by simp)
        have hs' : ∀ b ∈ s, 1 ≤ b := by
          intro b hb
          exact hs b (by simp [hb])
        simpa [Nat.add_comm] using Nat.add_le_add ha (ih hs')
  exact h σ.cycleType fun _ ha =>
    Nat.le_of_lt (Equiv.Perm.one_lt_of_mem_cycleType ha)

private theorem cycleDefect_mod_two {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) :
    (σ.cycleType.sum + σ.cycleType.card) % 2 = cycleDefect σ % 2 := by
  have hle := cycleType_card_le_sum σ
  rw [cycleDefect]
  omega

private theorem exchangeUnitWeight_sign_eq_cycleWeight {α R : Type*}
    [Fintype α] [DecidableEq α] [CommSemiring R]
    (ζ : R) (hζ : ζ * ζ = 1) (σ : Equiv.Perm α) :
    exchangeUnitWeight ζ (Equiv.Perm.sign σ) = ζ ^ cycleDefect σ := by
  rw [Equiv.Perm.sign_of_cycleType, exchangeUnitWeight_neg_one_pow ζ hζ]
  exact pow_eq_of_mod_two_eq hζ (cycleDefect_mod_two σ)

/-! ## Private pairing ↔ permutation implementation -/

private def sidePartner (e : SideSplitting m) (σ : Equiv.Perm (Fin m)) :
    Equiv.Perm (Fin (2 * m)) :=
  ((e.symm.trans ((Equiv.sumComm (Fin m) (Fin m)).trans (Equiv.sumCongr σ.symm σ))).trans e)

@[simp]
private theorem sidePartner_inl (e : SideSplitting m) (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    sidePartner e σ (e (Sum.inl i)) = e (Sum.inr (σ i)) := by
  simp [sidePartner]

@[simp]
private theorem sidePartner_inr (e : SideSplitting m) (σ : Equiv.Perm (Fin m)) (j : Fin m) :
    sidePartner e σ (e (Sum.inr j)) = e (Sum.inl (σ.symm j)) := by
  simp [sidePartner]

private theorem isPairing_sidePartner (e : SideSplitting m) (σ : Equiv.Perm (Fin m)) :
    IsPairing (sidePartner e σ) := by
  constructor
  · intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    cases y with
    | inl i => simp
    | inr j => simp
  · intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    cases y with
    | inl i =>
        intro h
        rw [sidePartner_inl] at h
        have h' := e.injective h
        simp at h'
    | inr j =>
        intro h
        rw [sidePartner_inr] at h
        have h' := e.injective h
        simp at h'

private def sidePairing (e : SideSplitting m) (σ : Equiv.Perm (Fin m)) : Pairing m :=
  Pairing.ofPartner (sidePartner e σ) (isPairing_sidePartner e σ)

@[simp]
private theorem sidePairing_partner (e : SideSplitting m) (σ : Equiv.Perm (Fin m)) :
    (sidePairing e σ).partner = sidePartner e σ :=
  rfl

private theorem isBipartite_sidePairing (e : SideSplitting m) (σ : Equiv.Perm (Fin m)) :
    (sidePairing e σ).IsBipartite e :=
  fun i => ⟨σ i, by simp⟩

private theorem sidePairing_sideMatching (e : SideSplitting m) {P : Pairing m}
    (h : P.IsBipartite e) : sidePairing e (P.sideMatching e h) = P := by
  refine Pairing.ext (Equiv.ext fun x => ?_)
  obtain ⟨y, rfl⟩ := e.surjective x
  cases y with
  | inl i => rw [sidePairing_partner, sidePartner_inl, ← Pairing.partner_sideMatching e h i]
  | inr j =>
      rw [sidePairing_partner, sidePartner_inr]
      have hi := Pairing.partner_sideMatching e h ((P.sideMatching e h).symm j)
      rw [Equiv.apply_symm_apply] at hi
      rw [← hi, P.partner_partner]

private theorem sideSplitting_inl_ne_inr (e : SideSplitting m) (i j : Fin m) :
    e (Sum.inl i) ≠ e (Sum.inr j) := fun h => by simpa using e.injective h

private noncomputable def sidePair (e : SideSplitting m) (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    Fin (2 * m) × Fin (2 * m) :=
  if e (Sum.inl i) < e (Sum.inr (σ i)) then (e (Sum.inl i), e (Sum.inr (σ i)))
  else (e (Sum.inr (σ i)), e (Sum.inl i))

private theorem sidePair_of_lt {e : SideSplitting m} {σ : Equiv.Perm (Fin m)} {i : Fin m}
    (h : e (Sum.inl i) < e (Sum.inr (σ i))) :
    sidePair e σ i = (e (Sum.inl i), e (Sum.inr (σ i))) :=
  if_pos h

private theorem sidePair_of_gt {e : SideSplitting m} {σ : Equiv.Perm (Fin m)} {i : Fin m}
    (h : e (Sum.inr (σ i)) < e (Sum.inl i)) :
    sidePair e σ i = (e (Sum.inr (σ i)), e (Sum.inl i)) :=
  if_neg (asymm h)

private theorem sidePair_mem_pairs (e : SideSplitting m) (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    sidePair e σ i ∈ (sidePairing e σ).pairs := by
  rcases lt_trichotomy (e (Sum.inl i)) (e (Sum.inr (σ i))) with h | h | h
  · rw [sidePair, if_pos h]
    exact (Pairing.mem_pairs_iff _ _ _).2 ⟨h, by simp⟩
  · exact absurd h (sideSplitting_inl_ne_inr e i (σ i))
  · rw [sidePair, if_neg (asymm h)]
    refine (Pairing.mem_pairs_iff _ _ _).2 ⟨h, ?_⟩
    rw [sidePairing_partner, sidePartner_inr, Equiv.symm_apply_apply]

private noncomputable def sidePairEquiv (e : SideSplitting m) (σ : Equiv.Perm (Fin m)) :
    Fin m ≃ (sidePairing e σ).NormalizedPair := by
  refine Equiv.ofBijective (fun i => ⟨sidePair e σ i, sidePair_mem_pairs e σ i⟩) ⟨?_, ?_⟩
  · intro i j hij
    have hpair : sidePair e σ i = sidePair e σ j := congrArg Subtype.val hij
    have hmem : e (Sum.inl i) = (sidePair e σ j).1 ∨ e (Sum.inl i) = (sidePair e σ j).2 := by
      rw [← hpair, sidePair]
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hmem with h | h <;> rw [sidePair] at h <;> split_ifs at h
    · exact Sum.inl.inj (e.injective h)
    · exact absurd h (sideSplitting_inl_ne_inr e i (σ j))
    · exact absurd h (sideSplitting_inl_ne_inr e i (σ j))
    · exact Sum.inl.inj (e.injective h)
  · rintro ⟨⟨a, b⟩, hab⟩
    obtain ⟨hlt, hpartner⟩ := (Pairing.mem_pairs_iff _ _ _).1 hab
    obtain ⟨y, rfl⟩ := e.surjective a
    cases y with
    | inl i =>
        refine ⟨i, ?_⟩
        rw [sidePairing_partner, sidePartner_inl] at hpartner
        subst hpartner
        exact Subtype.ext (sidePair_of_lt hlt)
    | inr j =>
        rw [sidePairing_partner, sidePartner_inr] at hpartner
        subst hpartner
        have hgt : e (Sum.inr (σ (σ.symm j))) < e (Sum.inl (σ.symm j)) := by
          rwa [Equiv.apply_symm_apply]
        refine ⟨σ.symm j, Subtype.ext ?_⟩
        change sidePair e σ (σ.symm j) = (e (Sum.inr j), e (Sum.inl (σ.symm j)))
        rw [sidePair_of_gt hgt, Equiv.apply_symm_apply]

private theorem prod_sidePairing_pairs {R : Type*} [CommMonoid R] (e : SideSplitting m)
    (σ : Equiv.Perm (Fin m)) (f : Fin (2 * m) → Fin (2 * m) → R) :
    (∏ pr ∈ (sidePairing e σ).pairs, f pr.1 pr.2) =
      ∏ i : Fin m, f (sidePair e σ i).1 (sidePair e σ i).2 := by
  classical
  rw [Finset.prod_subtype (sidePairing e σ).pairs (fun _ => Iff.rfl)
    (fun pr => f pr.1 pr.2)]
  exact (Equiv.prod_comp (sidePairEquiv e σ) (fun pr => f pr.1.1 pr.1.2)).symm

/-! ## Private side-listing sign machinery -/

private def blockSideEquiv (m : ℕ) : Fin m × Fin 2 ≃ Fin m ⊕ Fin m where
  toFun p := if p.2 = 0 then Sum.inl p.1 else Sum.inr p.1
  invFun x := x.elim (fun i => (i, 0)) (fun i => (i, 1))
  left_inv p := by
    obtain ⟨i, s⟩ := p
    fin_cases s <;> simp
  right_inv x := by cases x <;> simp

private noncomputable def sideListingEquiv (m : ℕ) : Fin (2 * m) ≃ Fin m ⊕ Fin m :=
  (pairSlotIndexEquiv m).trans (blockSideEquiv m)

private noncomputable def sideListingPerm (e : SideSplitting m) (σ : Equiv.Perm (Fin m)) :
    Equiv.Perm (Fin (2 * m)) :=
  (sideListingEquiv m).trans ((Equiv.sumCongr (Equiv.refl (Fin m)) σ).trans e)

private theorem blockPair_sideListingPerm (e : SideSplitting m) (σ : Equiv.Perm (Fin m))
    (k : Fin m) :
    blockPair (sideListingPerm e σ) k = (e (Sum.inl k), e (Sum.inr (σ k))) := by
  change (sideListingPerm e σ ((pairSlotIndexEquiv m).symm (k, 0)),
      sideListingPerm e σ ((pairSlotIndexEquiv m).symm (k, 1))) =
      (e (Sum.inl k), e (Sum.inr (σ k)))
  simp [sideListingPerm, sideListingEquiv, blockSideEquiv]

private theorem sidePairing_presentsPairs (e : SideSplitting m) (σ : Equiv.Perm (Fin m)) :
    (sidePairing e σ).PresentsPairs (sideListingPerm e σ) := by
  refine ⟨sidePairEquiv e σ, fun k => ?_⟩
  rw [blockPair_sideListingPerm]
  rcases lt_trichotomy (e (Sum.inl k)) (e (Sum.inr (σ k))) with h | h | h
  · refine Or.inl ?_
    change (e (Sum.inl k), e (Sum.inr (σ k))) = sidePair e σ k
    rw [sidePair_of_lt h]
  · exact absurd h (sideSplitting_inl_ne_inr e k (σ k))
  · refine Or.inr ?_
    change (e (Sum.inl k), e (Sum.inr (σ k))) = (sidePair e σ k).swap
    rw [sidePair_of_gt h]
    rfl

private noncomputable def baseListingPerm (e : SideSplitting m) : Equiv.Perm (Fin (2 * m)) :=
  (sideListingEquiv m).trans e

private noncomputable def sumCongrListingPerm (m : ℕ) (σ : Equiv.Perm (Fin m)) :
    Equiv.Perm (Fin (2 * m)) :=
  (sideListingEquiv m).trans
    ((Equiv.sumCongr (Equiv.refl (Fin m)) σ).trans (sideListingEquiv m).symm)

private theorem sideListingPerm_eq (e : SideSplitting m) (σ : Equiv.Perm (Fin m)) :
    sideListingPerm e σ = (sumCongrListingPerm m σ).trans (baseListingPerm e) := by
  apply Equiv.ext
  intro x
  simp only [sideListingPerm, sumCongrListingPerm, baseListingPerm, sideListingEquiv,
    Equiv.trans_apply, Equiv.apply_symm_apply]

private theorem sign_sumCongrListingPerm (m : ℕ) (σ : Equiv.Perm (Fin m)) :
    Equiv.Perm.sign (sumCongrListingPerm m σ) = Equiv.Perm.sign σ := by
  have h := Equiv.Perm.sign_eq_sign_of_equiv (Equiv.sumCongr (Equiv.refl (Fin m)) σ)
    (sumCongrListingPerm m σ) (sideListingEquiv m).symm
    (fun x => by
      simp only [sumCongrListingPerm, Equiv.trans_apply, Equiv.apply_symm_apply])
  rw [← h, Equiv.Perm.sign_sumCongr]
  simp

private noncomputable def sideReversedCount (e : SideSplitting m)
    (σ : Equiv.Perm (Fin m)) : ℕ :=
  ∑ k : Fin m, if e (Sum.inr (σ k)) < e (Sum.inl k) then 1 else 0

private theorem neg_one_pow_crossingCount_eq_of_sidePairing (e : SideSplitting m)
    (σ : Equiv.Perm (Fin m)) :
    (-1 : ℤˣ) ^ (sidePairing e σ).crossingCount =
      Equiv.Perm.sign (baseListingPerm e) * (-1) ^ sideReversedCount e σ * Equiv.Perm.sign σ := by
  have hsign := (sidePairing e σ).sign_eq_of_presentsPairs (sideListingPerm e σ)
    (sidePairing_presentsPairs e σ)
  have hreversed : (∑ k : Fin m, if (blockPair (sideListingPerm e σ) k).2 <
      (blockPair (sideListingPerm e σ) k).1 then 1 else 0) = sideReversedCount e σ := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [blockPair_sideListingPerm]
  rw [hreversed] at hsign
  rw [sideListingPerm_eq, Equiv.Perm.sign_trans, sign_sumCongrListingPerm] at hsign
  have hsq : ((-1 : ℤˣ) ^ sideReversedCount e σ) * ((-1 : ℤˣ) ^ sideReversedCount e σ) = 1 :=
    Int.units_mul_self _
  calc
    (-1 : ℤˣ) ^ (sidePairing e σ).crossingCount =
        (-1 : ℤˣ) ^ sideReversedCount e σ *
          ((-1 : ℤˣ) ^ sideReversedCount e σ *
            (-1 : ℤˣ) ^ (sidePairing e σ).crossingCount) := by
      rw [← mul_assoc, hsq, one_mul]
    _ = (-1 : ℤˣ) ^ sideReversedCount e σ *
          (Equiv.Perm.sign (baseListingPerm e) * Equiv.Perm.sign σ) := by
      rw [← hsign]
    _ = Equiv.Perm.sign (baseListingPerm e) * (-1 : ℤˣ) ^ sideReversedCount e σ *
          Equiv.Perm.sign σ := by
      rw [← mul_assoc, mul_comm ((-1 : ℤˣ) ^ sideReversedCount e σ), mul_assoc]

/-- The splitting-dependent scalar factor in the exchange-sum reduction. Its internal construction
is deliberately hidden; callers only need that it depends on `ζ` and the chosen side splitting. -/
noncomputable def sideSplittingWeight {R : Type*} [CommSemiring R]
    (ζ : R) (e : SideSplitting m) : R :=
  exchangeUnitWeight ζ (Equiv.Perm.sign (baseListingPerm e))

private theorem pairingWeight_sidePairing {R : Type*} [CommSemiring R]
    (ζ : R) (hζ : ζ * ζ = 1) (e : SideSplitting m) (σ : Equiv.Perm (Fin m)) :
    ζ ^ (sidePairing e σ).crossingCount =
      sideSplittingWeight ζ e * ζ ^ sideReversedCount e σ * ζ ^ cycleDefect σ := by
  have h := congrArg (exchangeUnitWeight ζ)
    (neg_one_pow_crossingCount_eq_of_sidePairing e σ)
  simp only [exchangeUnitWeight_mul ζ hζ, exchangeUnitWeight_neg_one_pow ζ hζ] at h
  rw [exchangeUnitWeight_sign_eq_cycleWeight ζ hζ σ] at h
  simpa [sideSplittingWeight] using h

/-! ## Private selection rule and orientation absorption -/

private theorem exists_mem_pairs_inl_inl_of_not_isBipartite (e : SideSplitting m) {P : Pairing m}
    (h : ¬ P.IsBipartite e) :
    ∃ i i' : Fin m, (e (Sum.inl i), e (Sum.inl i')) ∈ P.pairs := by
  have h' : ∃ i : Fin m, ∀ j : Fin m, P.partner (e (Sum.inl i)) ≠ e (Sum.inr j) := by
    by_contra hc
    refine h fun i => ?_
    by_contra hi
    exact hc ⟨i, fun j hj => hi ⟨j, hj⟩⟩
  obtain ⟨i, hi⟩ := h'
  obtain ⟨y, hy⟩ := e.surjective (P.partner (e (Sum.inl i)))
  cases y with
  | inr j => exact absurd hy.symm (hi j)
  | inl i' =>
      have hpartner : P.partner (e (Sum.inl i)) = e (Sum.inl i') := hy.symm
      rcases lt_trichotomy (e (Sum.inl i)) (e (Sum.inl i')) with hlt | heq | hgt
      · exact ⟨i, i', (P.mem_pairs_iff _ _).2 ⟨hlt, hpartner⟩⟩
      · exact absurd (hpartner.trans heq.symm) (P.partner_ne _)
      · refine ⟨i', i, (P.mem_pairs_iff _ _).2 ⟨hgt, ?_⟩⟩
        rw [← hpartner, P.partner_partner]

private theorem prod_pairs_eq_zero_of_not_isBipartite {R : Type*} [CommMonoidWithZero R]
    (e : SideSplitting m) {P : Pairing m} (h : ¬ P.IsBipartite e)
    (pv : Fin (2 * m) → Fin (2 * m) → R)
    (hpv : ∀ i i' : Fin m, pv (e (Sum.inl i)) (e (Sum.inl i')) = 0) :
    (∏ pr ∈ P.pairs, pv pr.1 pr.2) = 0 := by
  obtain ⟨i, i', hmem⟩ := exists_mem_pairs_inl_inl_of_not_isBipartite e h
  exact Finset.prod_eq_zero hmem (hpv i i')

private theorem sum_pairings_eq_sum_perm_of_inl_vanishing {R : Type*} [CommSemiring R]
    (e : SideSplitting m) (w : Pairing m → R)
    (pv : Fin (2 * m) → Fin (2 * m) → R)
    (hpv : ∀ i i' : Fin m, pv (e (Sum.inl i)) (e (Sum.inl i')) = 0) :
    (∑ P : Pairing m, w P * ∏ pr ∈ P.pairs, pv pr.1 pr.2) =
      ∑ σ : Equiv.Perm (Fin m),
        w (sidePairing e σ) * ∏ i : Fin m, pv (sidePair e σ i).1 (sidePair e σ i).2 := by
  classical
  have hzero : ∀ P ∈ (Finset.univ : Finset (Pairing m)),
      P ∉ Finset.univ.filter (fun P : Pairing m => P.IsBipartite e) →
        w P * ∏ pr ∈ P.pairs, pv pr.1 pr.2 = 0 := by
    intro P _ hP
    have hnb : ¬ P.IsBipartite e := by simpa using hP
    rw [prod_pairs_eq_zero_of_not_isBipartite e hnb pv hpv, mul_zero]
  have himage : (Finset.univ.filter fun P : Pairing m => P.IsBipartite e) =
      Finset.univ.image (fun σ : Equiv.Perm (Fin m) => sidePairing e σ) := by
    ext P
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hP
      exact ⟨P.sideMatching e hP, sidePairing_sideMatching e hP⟩
    · rintro ⟨σ, rfl⟩
      exact isBipartite_sidePairing e σ
  have hinj : Set.InjOn (fun σ : Equiv.Perm (Fin m) => sidePairing e σ)
      (Finset.univ : Finset (Equiv.Perm (Fin m))) := by
    intro x _ y _ hxy
    refine Equiv.ext fun i => ?_
    have hp := congrArg (fun P : Pairing m => P.partner (e (Sum.inl i))) hxy
    simp only [sidePairing_partner, sidePartner_inl] at hp
    exact Sum.inr.inj (e.injective hp)
  rw [← Finset.sum_subset (Finset.filter_subset _ _) hzero, himage, Finset.sum_image hinj]
  exact Finset.sum_congr rfl fun σ _ => by rw [prod_sidePairing_pairs]

/-- The side-oriented pair-value matrix for exchange scalar `ζ`. -/
noncomputable def exchangeMatrix {R : Type*} [CommSemiring R]
    (ζ : R) (e : SideSplitting m) (pv : Fin (2 * m) → Fin (2 * m) → R) :
    Matrix (Fin m) (Fin m) R :=
  fun i j =>
    if e (Sum.inl i) < e (Sum.inr j) then
      pv (e (Sum.inl i)) (e (Sum.inr j))
    else
      ζ * pv (e (Sum.inr j)) (e (Sum.inl i))

private theorem pow_sideReversedCount_mul_prod_sidePair {R : Type*} [CommSemiring R]
    (ζ : R) (e : SideSplitting m) (pv : Fin (2 * m) → Fin (2 * m) → R)
    (σ : Equiv.Perm (Fin m)) :
    ζ ^ sideReversedCount e σ *
        ∏ i : Fin m, pv (sidePair e σ i).1 (sidePair e σ i).2 =
      ∏ i : Fin m, exchangeMatrix ζ e pv i (σ i) := by
  classical
  simp only [sideReversedCount]
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rcases lt_trichotomy (e (Sum.inl i)) (e (Sum.inr (σ i))) with h | h | h
  · rw [sidePair_of_lt h, exchangeMatrix, if_neg (asymm h), if_pos h, pow_zero, one_mul]
  · exact absurd h (sideSplitting_inl_ne_inr e i (σ i))
  · rw [sidePair_of_gt h, exchangeMatrix, if_pos h, if_neg (asymm h), pow_one]

/-- **Generic exchange-statistics reduction.** If the pair value vanishes on two left-side
positions, the crossing-weighted pairing sum reduces to the cycle-weighted permutation sum of the
side-oriented matrix, up to the factor fixed by the side splitting. The involutive hypothesis is
needed only to identify crossing parity with permutation cycle parity. -/
theorem pairingSum_eq_permutationSum_of_inl_vanishing {R : Type*} [CommSemiring R]
    (ζ : R) (hζ : ζ * ζ = 1) (e : SideSplitting m)
    (pv : Fin (2 * m) → Fin (2 * m) → R)
    (hpv : ∀ i i' : Fin m, pv (e (Sum.inl i)) (e (Sum.inl i')) = 0) :
    pairingSum ζ pv =
      sideSplittingWeight ζ e *
        permutationSum ζ (exchangeMatrix ζ e pv) Finset.univ := by
  classical
  change pairingSum ζ pv =
    sideSplittingWeight ζ e *
      permutationSum ζ (fun i j => exchangeMatrix ζ e pv i j) Finset.univ
  rw [pairingSum]
  simp only [Pairing.evaluation]
  rw [sum_pairings_eq_sum_perm_of_inl_vanishing e _ pv hpv,
    permutationSum_univ_eq_sum_perm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [pairingWeight_sidePairing ζ hζ e σ]
  rw [← pow_sideReversedCount_mul_prod_sidePair ζ e pv σ]
  ring

end Combinatorics
