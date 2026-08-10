import LeanCondensedMatter.Combinatorics.PerfectPairing.CrossingParity
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Permanent

set_option linter.style.header false

/-!
# Bipartite perfect pairings

Splitting the ambient positions `Fin (2 * m)` into a first and a second half of size `m`, every
permutation of `Fin m` determines a perfect pairing that matches each position of the first half
with a position of the second half, and every pairing with that property arises this way.

This is the representation in which a fermionic pairing sum becomes a determinant: the pairs are
indexed by a permutation rather than by a general matching, and each pair is automatically
normalized because the whole first half precedes the whole second half.
-/

namespace Combinatorics

variable {m : ℕ}

/-- Ambient positions of a pairing of `Fin (2 * m)`, split into a first and a second half. -/
def bipartiteHalfEquiv (m : ℕ) : Fin m ⊕ Fin m ≃ Fin (2 * m) :=
  finSumFinEquiv.trans (finCongr (two_mul m).symm)

@[simp]
theorem bipartiteHalfEquiv_inl_val (m : ℕ) (i : Fin m) :
    (bipartiteHalfEquiv m (Sum.inl i)).val = i.val := by
  simp [bipartiteHalfEquiv]

@[simp]
theorem bipartiteHalfEquiv_inr_val (m : ℕ) (i : Fin m) :
    (bipartiteHalfEquiv m (Sum.inr i)).val = m + i.val := by
  simp [bipartiteHalfEquiv]
  omega

/-- Every position of the first half precedes every position of the second half. -/
theorem bipartiteHalfEquiv_inl_lt_inr (m : ℕ) (i j : Fin m) :
    bipartiteHalfEquiv m (Sum.inl i) < bipartiteHalfEquiv m (Sum.inr j) := by
  have hi := i.isLt
  change (bipartiteHalfEquiv m (Sum.inl i)).val < (bipartiteHalfEquiv m (Sum.inr j)).val
  rw [bipartiteHalfEquiv_inl_val, bipartiteHalfEquiv_inr_val]
  omega

/-- Positions inside the first half compare as their indices do. -/
theorem bipartiteHalfEquiv_inl_lt_inl_iff (m : ℕ) (i j : Fin m) :
    bipartiteHalfEquiv m (Sum.inl i) < bipartiteHalfEquiv m (Sum.inl j) ↔ i < j := by
  change (bipartiteHalfEquiv m (Sum.inl i)).val < (bipartiteHalfEquiv m (Sum.inl j)).val ↔ _
  rw [bipartiteHalfEquiv_inl_val, bipartiteHalfEquiv_inl_val]
  exact Iff.rfl

/-- Positions inside the second half compare as their indices do. -/
theorem bipartiteHalfEquiv_inr_lt_inr_iff (m : ℕ) (i j : Fin m) :
    bipartiteHalfEquiv m (Sum.inr i) < bipartiteHalfEquiv m (Sum.inr j) ↔ i < j := by
  change (bipartiteHalfEquiv m (Sum.inr i)).val < (bipartiteHalfEquiv m (Sum.inr j)).val ↔ _
  rw [bipartiteHalfEquiv_inr_val, bipartiteHalfEquiv_inr_val]
  change _ ↔ i.val < j.val
  omega

/-- A *side splitting* of the ambient positions is an identification of `Fin (2 * m)` with two
labelled sides of size `m`. The two halves are the canonical example; a number-conserving diagram
uses its creation and annihilation legs instead. -/
abbrev SideSplitting (m : ℕ) := Fin m ⊕ Fin m ≃ Fin (2 * m)

/-- The involution sending each position on the left side to the position on the right side
selected by `σ`. -/
def sidePartner (e : SideSplitting m) (σ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (2 * m)) :=
  ((e.symm.trans ((Equiv.sumComm (Fin m) (Fin m)).trans (Equiv.sumCongr σ.symm σ))).trans e)

@[simp]
theorem sidePartner_inl (e : SideSplitting m) (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    sidePartner e σ (e (Sum.inl i)) = e (Sum.inr (σ i)) := by
  simp [sidePartner]

@[simp]
theorem sidePartner_inr (e : SideSplitting m) (σ : Equiv.Perm (Fin m)) (j : Fin m) :
    sidePartner e σ (e (Sum.inr j)) = e (Sum.inl (σ.symm j)) := by
  simp [sidePartner]

theorem isPairing_sidePartner (e : SideSplitting m) (σ : Equiv.Perm (Fin m)) :
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

/-- The perfect pairing matching the two sides of `e` through `σ`. -/
def sidePairing (e : SideSplitting m) (σ : Equiv.Perm (Fin m)) : Pairing m :=
  Pairing.ofPartner (sidePartner e σ) (isPairing_sidePartner e σ)

@[simp]
theorem sidePairing_partner (e : SideSplitting m) (σ : Equiv.Perm (Fin m)) :
    (sidePairing e σ).partner = sidePartner e σ :=
  rfl

/-- The involution sending each position of the first half to the position of the second half
selected by `σ`. -/
def bipartitePartner (σ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (2 * m)) :=
  sidePartner (bipartiteHalfEquiv m) σ

@[simp]
theorem bipartitePartner_inl (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    bipartitePartner σ (bipartiteHalfEquiv m (Sum.inl i)) =
      bipartiteHalfEquiv m (Sum.inr (σ i)) :=
  sidePartner_inl _ σ i

@[simp]
theorem bipartitePartner_inr (σ : Equiv.Perm (Fin m)) (j : Fin m) :
    bipartitePartner σ (bipartiteHalfEquiv m (Sum.inr j)) =
      bipartiteHalfEquiv m (Sum.inl (σ.symm j)) :=
  sidePartner_inr _ σ j

theorem isPairing_bipartitePartner (σ : Equiv.Perm (Fin m)) :
    IsPairing (bipartitePartner σ) :=
  isPairing_sidePartner _ σ

/-- The perfect pairing of `Fin (2 * m)` matching the first half to the second half through `σ`. -/
def bipartitePairing (σ : Equiv.Perm (Fin m)) : Pairing m :=
  sidePairing (bipartiteHalfEquiv m) σ

@[simp]
theorem bipartitePairing_partner (σ : Equiv.Perm (Fin m)) :
    (bipartitePairing σ).partner = bipartitePartner σ :=
  rfl

/-- The normalized pairs of a bipartite pairing are exactly the graph of `σ`, read across the two
halves. -/
theorem mem_bipartitePairing_pairs_iff (σ : Equiv.Perm (Fin m))
    (x y : Fin m ⊕ Fin m) :
    (bipartiteHalfEquiv m x, bipartiteHalfEquiv m y) ∈ (bipartitePairing σ).pairs ↔
      ∃ i : Fin m, x = Sum.inl i ∧ y = Sum.inr (σ i) := by
  rw [Pairing.mem_pairs_iff]
  constructor
  · rintro ⟨hlt, hpartner⟩
    cases x with
    | inl i =>
        refine ⟨i, rfl, ?_⟩
        rw [bipartitePairing_partner, bipartitePartner_inl] at hpartner
        exact ((bipartiteHalfEquiv m).injective hpartner).symm
    | inr j =>
        rw [bipartitePairing_partner, bipartitePartner_inr] at hpartner
        have hy := (bipartiteHalfEquiv m).injective hpartner
        subst hy
        exact absurd hlt (asymm (bipartiteHalfEquiv_inl_lt_inr m (σ.symm j) j))
  · rintro ⟨i, rfl, rfl⟩
    exact ⟨bipartiteHalfEquiv_inl_lt_inr m i (σ i), by simp⟩

/-- The normalized pair of `bipartitePairing σ` indexed by `i`. -/
def bipartitePair (σ : Equiv.Perm (Fin m)) (i : Fin m) : Fin (2 * m) × Fin (2 * m) :=
  (bipartiteHalfEquiv m (Sum.inl i), bipartiteHalfEquiv m (Sum.inr (σ i)))

theorem bipartitePair_mem_pairs (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    bipartitePair σ i ∈ (bipartitePairing σ).pairs :=
  (mem_bipartitePairing_pairs_iff σ (Sum.inl i) (Sum.inr (σ i))).2 ⟨i, rfl, rfl⟩

/-- Two bipartite pairs cross exactly when the permutation does *not* invert their indices. -/
theorem crosses_bipartitePair_iff (σ : Equiv.Perm (Fin m)) (i j : Fin m) :
    Crosses (bipartitePair σ i) (bipartitePair σ j) ↔ i < j ∧ σ i < σ j := by
  constructor
  · rintro ⟨h1, -, h3⟩
    exact ⟨(bipartiteHalfEquiv_inl_lt_inl_iff m i j).1 h1,
      (bipartiteHalfEquiv_inr_lt_inr_iff m (σ i) (σ j)).1 h3⟩
  · rintro ⟨hij, hperm⟩
    exact ⟨(bipartiteHalfEquiv_inl_lt_inl_iff m i j).2 hij,
      bipartiteHalfEquiv_inl_lt_inr m j (σ i),
      (bipartiteHalfEquiv_inr_lt_inr_iff m (σ i) (σ j)).2 hperm⟩

/-- The normalized pairs of a bipartite pairing are indexed by `Fin m`. -/
noncomputable def bipartitePairEquiv (σ : Equiv.Perm (Fin m)) :
    Fin m ≃ (bipartitePairing σ).NormalizedPair := by
  refine Equiv.ofBijective
    (fun i => ⟨bipartitePair σ i, bipartitePair_mem_pairs σ i⟩) ⟨?_, ?_⟩
  · intro i j h
    have hpair : bipartitePair σ i = bipartitePair σ j := congrArg Subtype.val h
    have hfirst : bipartiteHalfEquiv m (Sum.inl i) = bipartiteHalfEquiv m (Sum.inl j) :=
      congrArg Prod.fst hpair
    exact Sum.inl.inj ((bipartiteHalfEquiv m).injective hfirst)
  · rintro ⟨⟨a, b⟩, hab⟩
    obtain ⟨x, rfl⟩ := (bipartiteHalfEquiv m).surjective a
    obtain ⟨y, rfl⟩ := (bipartiteHalfEquiv m).surjective b
    obtain ⟨i, rfl, rfl⟩ := (mem_bipartitePairing_pairs_iff σ x y).1 hab
    exact ⟨i, rfl⟩

@[simp]
theorem bipartitePairEquiv_apply (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    (bipartitePairEquiv σ i).1 = bipartitePair σ i :=
  rfl

/-- Crossings of a bipartite pairing count the ordered index pairs that `σ` preserves. -/
theorem crossingCount_bipartitePairing (σ : Equiv.Perm (Fin m)) :
    (bipartitePairing σ).crossingCount =
      ∑ i : Fin m, ∑ j : Fin m, if i < j ∧ σ i < σ j then 1 else 0 := by
  classical
  rw [Pairing.crossingCount_eq_sum_sum_crosses, ← Equiv.sum_comp (bipartitePairEquiv σ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp (bipartitePairEquiv σ)]
  exact Finset.sum_congr rfl fun j _ => by
    simp only [bipartitePairEquiv_apply, crosses_bipartitePair_iff]

private theorem ite_one_neg_one_eq_pow (P : Prop) [Decidable P] :
    (if P then (1 : ℤˣ) else -1) = (-1) ^ (if P then 0 else 1) := by
  by_cases h : P <;> simp [h]

private theorem sum_ite_and_eq_sum_Ioi {m : ℕ} (i : Fin m) (P : Fin m → Prop)
    [DecidablePred P] :
    (∑ j : Fin m, if i < j ∧ P j then (1 : ℕ) else 0) =
      ∑ j ∈ Finset.Ioi i, if P j then 1 else 0 := by
  classical
  have hpointwise : ∀ j : Fin m,
      (if i < j ∧ P j then (1 : ℕ) else 0) = if i < j then (if P j then 1 else 0) else 0 := by
    intro j
    by_cases h1 : i < j <;> by_cases h2 : P j <;> simp [h1, h2]
  rw [Finset.sum_congr rfl fun j _ => hpointwise j, ← Finset.sum_filter]
  congr 1
  ext j
  simp

/-- Crossings of a bipartite pairing and inversions of the permutation are complementary, so the
pairing weight is the permutation sign up to a factor that does not depend on `σ`. -/
theorem neg_one_pow_crossingCount_mul_sign (σ : Equiv.Perm (Fin m)) :
    (-1 : ℤˣ) ^ (bipartitePairing σ).crossingCount * Equiv.Perm.sign σ =
      (-1) ^ ∑ i : Fin m, (Finset.Ioi i).card := by
  classical
  have hsign : Equiv.Perm.sign σ =
      (-1 : ℤˣ) ^ ∑ i : Fin m, ∑ j ∈ Finset.Ioi i, (if σ i < σ j then 0 else 1) := by
    rw [Equiv.Perm.sign_eq_prod_prod_Ioi, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun j _ => ite_one_neg_one_eq_pow _
  have hcross : (bipartitePairing σ).crossingCount =
      ∑ i : Fin m, ∑ j ∈ Finset.Ioi i, (if σ i < σ j then 1 else 0) := by
    rw [crossingCount_bipartitePairing]
    exact Finset.sum_congr rfl fun i _ => sum_ite_and_eq_sum_Ioi i _
  rw [hcross, hsign, ← pow_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib, Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : σ i < σ j <;> simp [h]

/-- Solved form of `neg_one_pow_crossingCount_mul_sign`: the bipartite pairing weight is the
permutation sign scaled by a factor independent of `σ`. -/
theorem neg_one_pow_crossingCount_eq_mul_sign (σ : Equiv.Perm (Fin m)) :
    (-1 : ℤˣ) ^ (bipartitePairing σ).crossingCount =
      (-1) ^ (∑ i : Fin m, (Finset.Ioi i).card) * Equiv.Perm.sign σ := by
  have h := neg_one_pow_crossingCount_mul_sign σ
  calc (-1 : ℤˣ) ^ (bipartitePairing σ).crossingCount
      = (-1 : ℤˣ) ^ (bipartitePairing σ).crossingCount *
          (Equiv.Perm.sign σ * Equiv.Perm.sign σ) := by
        rw [Int.units_mul_self, mul_one]
    _ = ((-1 : ℤˣ) ^ (bipartitePairing σ).crossingCount * Equiv.Perm.sign σ) *
          Equiv.Perm.sign σ := (mul_assoc _ _ _).symm
    _ = (-1) ^ (∑ i : Fin m, (Finset.Ioi i).card) * Equiv.Perm.sign σ := by rw [h]

section Matrix

variable {R : Type*} [CommRing R]

private theorem neg_one_pow_crossingCount_cast (σ : Equiv.Perm (Fin m)) :
    (-1 : R) ^ (bipartitePairing σ).crossingCount =
      (-1 : R) ^ (∑ i : Fin m, (Finset.Ioi i).card) *
        ((Equiv.Perm.sign σ : ℤ) : R) := by
  have hz := congrArg (fun u : ℤˣ => ((u : ℤ) : R))
    (neg_one_pow_crossingCount_eq_mul_sign σ)
  simpa using hz

private theorem det_eq_sum_sign_mul_prod (K : Matrix (Fin m) (Fin m) R) :
    K.det = ∑ σ : Equiv.Perm (Fin m),
      ((Equiv.Perm.sign σ : ℤ) : R) * ∏ i, K i (σ i) := by
  rw [← Matrix.det_transpose K, Matrix.det_apply']
  exact Finset.sum_congr rfl fun σ _ => by simp

/-- **Fermionic bipartite pairing sum as a determinant.** Weighting each bipartite pairing by the
fermionic exchange sign and multiplying the matrix entries of its pairs gives the determinant, up to
the factor that does not depend on the pairing. -/
theorem sum_neg_one_pow_crossingCount_mul_prod (K : Matrix (Fin m) (Fin m) R) :
    (∑ σ : Equiv.Perm (Fin m),
        (-1 : R) ^ (bipartitePairing σ).crossingCount * ∏ i, K i (σ i)) =
      (-1 : R) ^ (∑ i : Fin m, (Finset.Ioi i).card) * K.det := by
  calc (∑ σ : Equiv.Perm (Fin m),
          (-1 : R) ^ (bipartitePairing σ).crossingCount * ∏ i, K i (σ i))
      = ∑ σ : Equiv.Perm (Fin m),
          (-1 : R) ^ (∑ i : Fin m, (Finset.Ioi i).card) *
            (((Equiv.Perm.sign σ : ℤ) : R) * ∏ i, K i (σ i)) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [neg_one_pow_crossingCount_cast σ, mul_assoc]
    _ = (-1 : R) ^ (∑ i : Fin m, (Finset.Ioi i).card) *
          ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : R) * ∏ i, K i (σ i) :=
        (Finset.mul_sum _ _ _).symm
    _ = (-1 : R) ^ (∑ i : Fin m, (Finset.Ioi i).card) * K.det := by
        rw [← det_eq_sum_sign_mul_prod]

/-- **Bosonic bipartite pairing sum as a permanent.** Without an exchange sign the same sum is the
permanent. -/
theorem sum_prod_eq_permanent (K : Matrix (Fin m) (Fin m) R) :
    (∑ σ : Equiv.Perm (Fin m), ∏ i, K i (σ i)) = K.permanent := by
  rw [← Matrix.permanent_transpose K, Matrix.permanent]
  exact Finset.sum_congr rfl fun σ _ => by simp

end Matrix

/-- A pairing is *bipartite* for a side splitting when every left position is matched to a right
one. The converse is automatic: both sides are finite of the same size and the partner map is
injective. -/
def Pairing.IsBipartite (e : SideSplitting m) (P : Pairing m) : Prop :=
  ∀ i : Fin m, ∃ j : Fin m, P.partner (e (Sum.inl i)) = e (Sum.inr j)

theorem isBipartite_sidePairing (e : SideSplitting m) (σ : Equiv.Perm (Fin m)) :
    (sidePairing e σ).IsBipartite e :=
  fun i => ⟨σ i, by simp⟩

private noncomputable def matchingTo (e : SideSplitting m) {P : Pairing m}
    (h : P.IsBipartite e) (i : Fin m) : Fin m :=
  Classical.choose (h i)

private theorem matchingTo_spec (e : SideSplitting m) {P : Pairing m} (h : P.IsBipartite e)
    (i : Fin m) : P.partner (e (Sum.inl i)) = e (Sum.inr (matchingTo e h i)) :=
  Classical.choose_spec (h i)

private theorem matchingTo_injective (e : SideSplitting m) {P : Pairing m}
    (h : P.IsBipartite e) : Function.Injective (matchingTo e h) := by
  intro i j hij
  have hspec := matchingTo_spec e h i
  rw [hij, ← matchingTo_spec e h j] at hspec
  exact Sum.inl.inj (e.injective (P.partner.injective hspec))

/-- The permutation matching the two sides of a bipartite pairing. -/
noncomputable def Pairing.sideMatching (e : SideSplitting m) {P : Pairing m}
    (h : P.IsBipartite e) : Equiv.Perm (Fin m) :=
  Equiv.ofBijective (matchingTo e h) (matchingTo_injective e h).bijective_of_finite

@[simp]
theorem Pairing.partner_sideMatching (e : SideSplitting m) {P : Pairing m}
    (h : P.IsBipartite e) (i : Fin m) :
    P.partner (e (Sum.inl i)) = e (Sum.inr (P.sideMatching e h i)) :=
  matchingTo_spec e h i

theorem sidePairing_sideMatching (e : SideSplitting m) {P : Pairing m} (h : P.IsBipartite e) :
    sidePairing e (P.sideMatching e h) = P := by
  refine Pairing.ext (Equiv.ext fun x => ?_)
  obtain ⟨y, rfl⟩ := e.surjective x
  cases y with
  | inl i => rw [sidePairing_partner, sidePartner_inl, ← Pairing.partner_sideMatching e h i]
  | inr j =>
      rw [sidePairing_partner, sidePartner_inr]
      have hi := Pairing.partner_sideMatching e h ((P.sideMatching e h).symm j)
      rw [Equiv.apply_symm_apply] at hi
      rw [← hi, P.partner_partner]

theorem sideMatching_sidePairing (e : SideSplitting m) (σ : Equiv.Perm (Fin m)) :
    (sidePairing e σ).sideMatching e (isBipartite_sidePairing e σ) = σ := by
  refine Equiv.ext fun i => ?_
  have h := Pairing.partner_sideMatching e (isBipartite_sidePairing e σ) i
  rw [sidePairing_partner, sidePartner_inl] at h
  exact (Sum.inr.inj (e.injective h)).symm

/-- **Bipartite pairings are exactly permutations.** For a side splitting of the ambient positions,
the pairings matching the two sides correspond to the permutations of one side. -/
noncomputable def sidePairingEquiv (e : SideSplitting m) :
    Equiv.Perm (Fin m) ≃ {P : Pairing m // P.IsBipartite e} where
  toFun σ := ⟨sidePairing e σ, isBipartite_sidePairing e σ⟩
  invFun P := P.1.sideMatching e P.2
  left_inv σ := sideMatching_sidePairing e σ
  right_inv P := Subtype.ext (sidePairing_sideMatching e P.2)

theorem sideSplitting_inl_ne_inr (e : SideSplitting m) (i j : Fin m) :
    e (Sum.inl i) ≠ e (Sum.inr j) := fun h => by simpa using e.injective h

/-- The normalized pair of `sidePairing e σ` indexed by `i`, written in position order. Which side
comes first depends on the splitting, so both orientations occur. -/
noncomputable def sidePair (e : SideSplitting m) (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    Fin (2 * m) × Fin (2 * m) :=
  if e (Sum.inl i) < e (Sum.inr (σ i)) then (e (Sum.inl i), e (Sum.inr (σ i)))
  else (e (Sum.inr (σ i)), e (Sum.inl i))

theorem sidePair_mem_pairs (e : SideSplitting m) (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    sidePair e σ i ∈ (sidePairing e σ).pairs := by
  rcases lt_trichotomy (e (Sum.inl i)) (e (Sum.inr (σ i))) with h | h | h
  · rw [sidePair, if_pos h]
    exact (Pairing.mem_pairs_iff _ _ _).2 ⟨h, by simp⟩
  · exact absurd h (sideSplitting_inl_ne_inr e i (σ i))
  · rw [sidePair, if_neg (asymm h)]
    refine (Pairing.mem_pairs_iff _ _ _).2 ⟨h, ?_⟩
    rw [sidePairing_partner, sidePartner_inr, Equiv.symm_apply_apply]

/-- The normalized pairs of a bipartite pairing are indexed by the side it matches from. -/
noncomputable def sidePairEquiv (e : SideSplitting m) (σ : Equiv.Perm (Fin m)) :
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
        exact Subtype.ext (by rw [sidePair, if_pos hlt])
    | inr j =>
        refine ⟨σ.symm j, ?_⟩
        rw [sidePairing_partner, sidePartner_inr] at hpartner
        subst hpartner
        refine Subtype.ext ?_
        rw [sidePair, Equiv.apply_symm_apply, if_neg (asymm hlt)]

/-- A product over the pairs of a bipartite pairing is a product over the matching permutation,
each pair evaluated in whichever order the splitting puts it. -/
theorem prod_sidePairing_pairs {R : Type*} [CommMonoid R] (e : SideSplitting m)
    (σ : Equiv.Perm (Fin m)) (f : Fin (2 * m) → Fin (2 * m) → R) :
    (∏ pr ∈ (sidePairing e σ).pairs, f pr.1 pr.2) =
      ∏ i : Fin m, f (sidePair e σ i).1 (sidePair e σ i).2 := by
  classical
  rw [Finset.prod_subtype (sidePairing e σ).pairs (fun _ => Iff.rfl)
    (fun pr => f pr.1 pr.2)]
  exact (Equiv.prod_comp (sidePairEquiv e σ) (fun pr => f pr.1.1 pr.1.2)).symm

end Combinatorics
