import LeanCondensedMatter.Combinatorics.PerfectPairing.Sign

set_option linter.style.header false

/-!
# Splitting a pairing along a decomposition of its positions

A *position splitting* presents the ambient positions of a pairing of `Fin (2 * n)` as two labelled
parts carrying `a` and `b` pairs. A pairing is *split* by it when no pair crosses between the parts;
such a pairing restricts to a pairing of each part.

This is the decomposition a connected-component factorization uses: the pairs of a Wick diagram
never join two different connected components, so the diagram's pairing restricts to each component.

Only the left part needs to be assumed closed under `partner`. Closure of the right part is
automatic, because `partner` is an involution: a right position paired to a left one would make that
left position paired to a right one.

Restricting and assembling are mutually inverse, so the pairings split by a given splitting are
exactly the pairs of pairings of the parts (`Pairing.splitEquiv`).

Compare `Combinatorics.SideSplitting`, where the pairs all *do* cross between the two parts. The two
are the extreme cases of the same presentation of the positions.
-/

namespace Combinatorics

variable {a b n : ℕ}

/-- A presentation of the ambient positions of a pairing of `Fin (2 * n)` as two parts carrying `a`
and `b` pairs. -/
abbrev PositionSplitting (a b n : ℕ) := Fin (2 * a) ⊕ Fin (2 * b) ≃ Fin (2 * n)

/-- A pairing is *split* by a position splitting when the left part is closed under `partner`, so
that no pair joins the two parts. -/
def Pairing.IsSplit (e : PositionSplitting a b n) (P : Pairing n) : Prop :=
  ∀ i : Fin (2 * a), ∃ j : Fin (2 * a), P.partner (e (Sum.inl i)) = e (Sum.inl j)

theorem positionSplitting_inl_ne_inr (e : PositionSplitting a b n) (i : Fin (2 * a))
    (j : Fin (2 * b)) : e (Sum.inl i) ≠ e (Sum.inr j) := fun h => by simpa using e.injective h

/-- **The right part is closed automatically.** A right position paired to a left one would make
that left position paired to a right one, contradicting the left closure. -/
theorem Pairing.isSplit_inr (e : PositionSplitting a b n) {P : Pairing n} (h : P.IsSplit e)
    (i : Fin (2 * b)) : ∃ j : Fin (2 * b), P.partner (e (Sum.inr i)) = e (Sum.inr j) := by
  obtain ⟨y, hy⟩ := e.surjective (P.partner (e (Sum.inr i)))
  cases y with
  | inr j => exact ⟨j, hy.symm⟩
  | inl k =>
      obtain ⟨j, hj⟩ := h k
      have hback : P.partner (e (Sum.inl k)) = e (Sum.inr i) := by
        rw [hy, P.partner_partner]
      exact absurd (hback.symm.trans hj) (Ne.symm (positionSplitting_inl_ne_inr e j i))

section Left

variable (e : PositionSplitting a b n) {P : Pairing n} (h : P.IsSplit e)

/-- The partner of a left position, read back in the left part. -/
private noncomputable def splitLeftMap (i : Fin (2 * a)) : Fin (2 * a) :=
  Classical.choose (h i)

private theorem splitLeftMap_spec (i : Fin (2 * a)) :
    P.partner (e (Sum.inl i)) = e (Sum.inl (splitLeftMap e h i)) :=
  Classical.choose_spec (h i)

private theorem splitLeftMap_involutive : Function.Involutive (splitLeftMap e h) := by
  intro i
  have h1 := splitLeftMap_spec e h i
  have h2 := splitLeftMap_spec e h (splitLeftMap e h i)
  have : e (Sum.inl i) = e (Sum.inl (splitLeftMap e h (splitLeftMap e h i))) := by
    rw [← h2, ← h1, P.partner_partner]
  exact (Sum.inl.inj (e.injective this)).symm

private theorem splitLeftMap_ne_self (i : Fin (2 * a)) : splitLeftMap e h i ≠ i := by
  intro hi
  have := splitLeftMap_spec e h i
  rw [hi] at this
  exact absurd this (P.partner_ne _)

/-- The pairing induced on the left part. -/
noncomputable def Pairing.splitLeft : Pairing a :=
  Pairing.ofPartner (Function.Involutive.toPerm _ (splitLeftMap_involutive e h))
    ⟨splitLeftMap_involutive e h, splitLeftMap_ne_self e h⟩

/-- The induced left pairing is read off the ambient partner map. -/
@[simp]
theorem Pairing.partner_splitLeft (i : Fin (2 * a)) :
    P.partner (e (Sum.inl i)) = e (Sum.inl ((P.splitLeft e h).partner i)) :=
  splitLeftMap_spec e h i

end Left

section Right

variable (e : PositionSplitting a b n) {P : Pairing n} (h : P.IsSplit e)

/-- The partner of a right position, read back in the right part. -/
private noncomputable def splitRightMap (i : Fin (2 * b)) : Fin (2 * b) :=
  Classical.choose (P.isSplit_inr e h i)

private theorem splitRightMap_spec (i : Fin (2 * b)) :
    P.partner (e (Sum.inr i)) = e (Sum.inr (splitRightMap e h i)) :=
  Classical.choose_spec (P.isSplit_inr e h i)

private theorem splitRightMap_involutive : Function.Involutive (splitRightMap e h) := by
  intro i
  have h1 := splitRightMap_spec e h i
  have h2 := splitRightMap_spec e h (splitRightMap e h i)
  have : e (Sum.inr i) = e (Sum.inr (splitRightMap e h (splitRightMap e h i))) := by
    rw [← h2, ← h1, P.partner_partner]
  exact (Sum.inr.inj (e.injective this)).symm

private theorem splitRightMap_ne_self (i : Fin (2 * b)) : splitRightMap e h i ≠ i := by
  intro hi
  have := splitRightMap_spec e h i
  rw [hi] at this
  exact absurd this (P.partner_ne _)

/-- The pairing induced on the right part. -/
noncomputable def Pairing.splitRight : Pairing b :=
  Pairing.ofPartner (Function.Involutive.toPerm _ (splitRightMap_involutive e h))
    ⟨splitRightMap_involutive e h, splitRightMap_ne_self e h⟩

/-- The induced right pairing is read off the ambient partner map. -/
@[simp]
theorem Pairing.partner_splitRight (i : Fin (2 * b)) :
    P.partner (e (Sum.inr i)) = e (Sum.inr ((P.splitRight e h).partner i)) :=
  splitRightMap_spec e h i

end Right

section Assemble

private theorem sumCongr_involutive {α β : Type*} (p : Equiv.Perm α) (q : Equiv.Perm β)
    (hp : Function.Involutive p) (hq : Function.Involutive q) :
    Function.Involutive (Equiv.sumCongr p q) := by
  rintro (x | x)
  · exact congrArg Sum.inl (hp x)
  · exact congrArg Sum.inr (hq x)

private theorem sumCongr_ne_self {α β : Type*} (p : Equiv.Perm α) (q : Equiv.Perm β)
    (hp : ∀ x, p x ≠ x) (hq : ∀ x, q x ≠ x) (x : α ⊕ β) :
    Equiv.sumCongr p q x ≠ x := by
  rcases x with x | x
  · exact fun h => hp x (Sum.inl.inj h)
  · exact fun h => hq x (Sum.inr.inj h)

private theorem permCongr_involutive {α β : Type*} (e : α ≃ β)
    (p : Equiv.Perm α) (hp : Function.Involutive p) :
    Function.Involutive (e.permCongr p) := by
  intro x
  simp [Equiv.permCongr_apply, hp (e.symm x)]

private theorem permCongr_ne_self {α β : Type*} (e : α ≃ β)
    (p : Equiv.Perm α) (hp : ∀ x, p x ≠ x) (x : β) :
    e.permCongr p x ≠ x := by
  intro h
  rw [Equiv.permCongr_apply, Equiv.apply_eq_iff_eq_symm_apply] at h
  exact hp _ h

/-- **Assemble a pairing from a pairing on each part.** Inverse construction to `splitLeft` and
`splitRight`: no pair joins the two parts, so the two partner maps can simply be run side by side. -/
noncomputable def Pairing.ofSplit (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b) :
    Pairing n :=
  Pairing.ofPartner (e.permCongr (Equiv.sumCongr P.partner Q.partner))
    ⟨permCongr_involutive _ _
        (sumCongr_involutive _ _ P.partner_involutive Q.partner_involutive),
      permCongr_ne_self _ _
        (sumCongr_ne_self _ _ P.partner_ne_self Q.partner_ne_self)⟩

@[simp]
theorem Pairing.ofSplit_partner_inl (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b)
    (i : Fin (2 * a)) :
    (Pairing.ofSplit e P Q).partner (e (Sum.inl i)) = e (Sum.inl (P.partner i)) := by
  change e (Equiv.sumCongr P.partner Q.partner (e.symm (e (Sum.inl i)))) = _
  rw [e.symm_apply_apply]
  rfl

@[simp]
theorem Pairing.ofSplit_partner_inr (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b)
    (i : Fin (2 * b)) :
    (Pairing.ofSplit e P Q).partner (e (Sum.inr i)) = e (Sum.inr (Q.partner i)) := by
  change e (Equiv.sumCongr P.partner Q.partner (e.symm (e (Sum.inr i)))) = _
  rw [e.symm_apply_apply]
  rfl

/-- An assembled pairing is split by the splitting it was assembled along. -/
theorem Pairing.isSplit_ofSplit (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b) :
    (Pairing.ofSplit e P Q).IsSplit e := fun i =>
  ⟨P.partner i, Pairing.ofSplit_partner_inl e P Q i⟩

/-- Orient a pair by the ambient linear order, so that it is listed the way `Pairing.pairs` lists
it. -/
def orientPair {α : Type*} [LinearOrder α] (u v : α) : α × α :=
  if u < v then (u, v) else (v, u)

/-- Two distinct partners form a pair, whichever way round they are given. -/
theorem mem_pairs_orientPair {m : ℕ} (P : Pairing m) {u v : Fin (2 * m)}
    (hne : u ≠ v) (hpartner : P.partner u = v) :
    orientPair u v ∈ P.pairs := by
  unfold orientPair
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [if_pos hlt]
    exact (P.mem_pairs_iff u v).2 ⟨hlt, hpartner⟩
  · rw [if_neg (asymm hgt)]
    refine (P.mem_pairs_iff v u).2 ⟨hgt, ?_⟩
    rw [← hpartner, P.partner_partner]

/-- **A left part's pair transports to a pair of the assembled pairing.** -/
theorem mem_pairs_ofSplit_inl (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b)
    {pr : Fin (2 * a) × Fin (2 * a)} (hpr : pr ∈ P.pairs) :
    orientPair (e (Sum.inl pr.1)) (e (Sum.inl pr.2)) ∈ (Pairing.ofSplit e P Q).pairs := by
  obtain ⟨u, v⟩ := pr
  obtain ⟨hlt, hpartner⟩ := (P.mem_pairs_iff u v).1 hpr
  refine mem_pairs_orientPair _ (fun hEq => ?_) ?_
  · exact absurd (Sum.inl.inj (e.injective hEq)) (ne_of_lt hlt)
  · rw [Pairing.ofSplit_partner_inl, hpartner]

/-- **A right part's pair transports to a pair of the assembled pairing.** -/
theorem mem_pairs_ofSplit_inr (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b)
    {pr : Fin (2 * b) × Fin (2 * b)} (hpr : pr ∈ Q.pairs) :
    orientPair (e (Sum.inr pr.1)) (e (Sum.inr pr.2)) ∈ (Pairing.ofSplit e P Q).pairs := by
  obtain ⟨u, v⟩ := pr
  obtain ⟨hlt, hpartner⟩ := (Q.mem_pairs_iff u v).1 hpr
  refine mem_pairs_orientPair _ (fun hEq => ?_) ?_
  · exact absurd (Sum.inr.inj (e.injective hEq)) (ne_of_lt hlt)
  · rw [Pairing.ofSplit_partner_inr, hpartner]

theorem orientPair_cases {α : Type*} [LinearOrder α] (u v : α) :
    orientPair u v = (u, v) ∨ orientPair u v = (v, u) := by
  unfold orientPair
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- A splitting forces the two part sizes to add up. -/
theorem PositionSplitting.card_add (e : PositionSplitting a b n) : a + b = n := by
  have h := Fintype.card_congr e
  simp only [Fintype.card_sum, Fintype.card_fin] at h
  omega

/-- The map carrying each part's pairs to the assembled pairing's pairs. -/
noncomputable def splitPairsMap (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b) :
    ↥P.pairs ⊕ ↥Q.pairs → ↥(Pairing.ofSplit e P Q).pairs :=
  Sum.elim
    (fun pr => ⟨orientPair (e (Sum.inl pr.1.1)) (e (Sum.inl pr.1.2)),
      mem_pairs_ofSplit_inl e P Q pr.2⟩)
    (fun pr => ⟨orientPair (e (Sum.inr pr.1.1)) (e (Sum.inr pr.1.2)),
      mem_pairs_ofSplit_inr e P Q pr.2⟩)

private theorem splitPairsMap_injective (e : PositionSplitting a b n) (P : Pairing a)
    (Q : Pairing b) : Function.Injective (splitPairsMap e P Q) := by
  have key : ∀ {m : ℕ} {R : Pairing m} {pr pr' : Fin (2 * m) × Fin (2 * m)},
      pr ∈ R.pairs → pr' ∈ R.pairs →
      (pr.1 = pr'.1 ∧ pr.2 = pr'.2) ∨ (pr.1 = pr'.2 ∧ pr.2 = pr'.1) → pr = pr' := by
    intro m R pr pr' hpr hpr' hcase
    obtain ⟨hlt, -⟩ := (R.mem_pairs_iff pr.1 pr.2).1 (by simpa using hpr)
    obtain ⟨hlt', -⟩ := (R.mem_pairs_iff pr'.1 pr'.2).1 (by simpa using hpr')
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exact absurd (h1 ▸ h2 ▸ hlt) (asymm hlt')
  rintro (⟨pr, hpr⟩ | ⟨pr, hpr⟩) (⟨pr', hpr'⟩ | ⟨pr', hpr'⟩) heq <;>
    simp only [splitPairsMap, Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq] at heq
  · refine congrArg Sum.inl (Subtype.ext (key hpr hpr' ?_))
    rcases orientPair_cases (e (Sum.inl pr.1)) (e (Sum.inl pr.2)) with h | h <;>
      rcases orientPair_cases (e (Sum.inl pr'.1)) (e (Sum.inl pr'.2)) with h' | h' <;>
      rw [h, h'] at heq
    · exact Or.inl ⟨Sum.inl.inj (e.injective (congrArg Prod.fst heq)),
        Sum.inl.inj (e.injective (congrArg Prod.snd heq))⟩
    · exact Or.inr ⟨Sum.inl.inj (e.injective (congrArg Prod.fst heq)),
        Sum.inl.inj (e.injective (congrArg Prod.snd heq))⟩
    · exact Or.inr ⟨Sum.inl.inj (e.injective (congrArg Prod.snd heq)),
        Sum.inl.inj (e.injective (congrArg Prod.fst heq))⟩
    · exact Or.inl ⟨Sum.inl.inj (e.injective (congrArg Prod.snd heq)),
        Sum.inl.inj (e.injective (congrArg Prod.fst heq))⟩
  · exact absurd (congrArg Prod.fst heq) (by
      rcases orientPair_cases (e (Sum.inl pr.1)) (e (Sum.inl pr.2)) with h | h <;>
        rcases orientPair_cases (e (Sum.inr pr'.1)) (e (Sum.inr pr'.2)) with h' | h' <;>
        rw [h, h'] <;> exact positionSplitting_inl_ne_inr e _ _)
  · exact absurd (congrArg Prod.fst heq) (by
      rcases orientPair_cases (e (Sum.inr pr.1)) (e (Sum.inr pr.2)) with h | h <;>
        rcases orientPair_cases (e (Sum.inl pr'.1)) (e (Sum.inl pr'.2)) with h' | h' <;>
        rw [h, h'] <;> exact Ne.symm (positionSplitting_inl_ne_inr e _ _))
  · refine congrArg Sum.inr (Subtype.ext (key hpr hpr' ?_))
    rcases orientPair_cases (e (Sum.inr pr.1)) (e (Sum.inr pr.2)) with h | h <;>
      rcases orientPair_cases (e (Sum.inr pr'.1)) (e (Sum.inr pr'.2)) with h' | h' <;>
      rw [h, h'] at heq
    · exact Or.inl ⟨Sum.inr.inj (e.injective (congrArg Prod.fst heq)),
        Sum.inr.inj (e.injective (congrArg Prod.snd heq))⟩
    · exact Or.inr ⟨Sum.inr.inj (e.injective (congrArg Prod.fst heq)),
        Sum.inr.inj (e.injective (congrArg Prod.snd heq))⟩
    · exact Or.inr ⟨Sum.inr.inj (e.injective (congrArg Prod.snd heq)),
        Sum.inr.inj (e.injective (congrArg Prod.fst heq))⟩
    · exact Or.inl ⟨Sum.inr.inj (e.injective (congrArg Prod.snd heq)),
        Sum.inr.inj (e.injective (congrArg Prod.fst heq))⟩

/-- **The pairs of an assembled pairing are the pairs of the two parts.** -/
noncomputable def splitPairsEquiv (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b) :
    ↥P.pairs ⊕ ↥Q.pairs ≃ ↥(Pairing.ofSplit e P Q).pairs :=
  Equiv.ofBijective (splitPairsMap e P Q)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨splitPairsMap_injective e P Q, by
        rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe, Fintype.card_coe,
          P.card_pairs, Q.card_pairs, (Pairing.ofSplit e P Q).card_pairs]
        exact e.card_add⟩)

end Assemble

section Inverse

/-- Assembling and then restricting to the left part returns the left pairing. -/
@[simp]
theorem Pairing.splitLeft_ofSplit (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b) :
    (Pairing.ofSplit e P Q).splitLeft e (Pairing.isSplit_ofSplit e P Q) = P := by
  refine Pairing.ext (Equiv.ext fun i => ?_)
  have h := Pairing.partner_splitLeft e (Pairing.isSplit_ofSplit e P Q) i
  rw [Pairing.ofSplit_partner_inl] at h
  exact (Sum.inl.inj (e.injective h)).symm

/-- Assembling and then restricting to the right part returns the right pairing. -/
@[simp]
theorem Pairing.splitRight_ofSplit (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b) :
    (Pairing.ofSplit e P Q).splitRight e (Pairing.isSplit_ofSplit e P Q) = Q := by
  refine Pairing.ext (Equiv.ext fun i => ?_)
  have h := Pairing.partner_splitRight e (Pairing.isSplit_ofSplit e P Q) i
  rw [Pairing.ofSplit_partner_inr] at h
  exact (Sum.inr.inj (e.injective h)).symm

/-- **A split pairing is assembled from its two restrictions.** Nothing is lost by taking a split
pairing apart: every position lies in one of the parts, and its partner lies in the same part. -/
theorem Pairing.ofSplit_splitLeft_splitRight (e : PositionSplitting a b n) {P : Pairing n}
    (h : P.IsSplit e) :
    Pairing.ofSplit e (P.splitLeft e h) (P.splitRight e h) = P := by
  refine Pairing.ext (Equiv.ext fun i => ?_)
  obtain ⟨x, rfl⟩ := e.surjective i
  cases x with
  | inl j => rw [Pairing.ofSplit_partner_inl, Pairing.partner_splitLeft e h]
  | inr j => rw [Pairing.ofSplit_partner_inr, Pairing.partner_splitRight e h]

/-- **The pairings split by a position splitting are exactly the pairs of part pairings.**

This is the combinatorial content of a binary diagram decomposition: choosing a pairing that
respects the splitting is the same as choosing one on each part independently. A reindexing of a sum
over diagrams as a sum over pairs of pieces goes through this equivalence. -/
noncomputable def Pairing.splitEquiv (e : PositionSplitting a b n) :
    {P : Pairing n // P.IsSplit e} ≃ Pairing a × Pairing b where
  toFun P := (P.1.splitLeft e P.2, P.1.splitRight e P.2)
  invFun PQ := ⟨Pairing.ofSplit e PQ.1 PQ.2, Pairing.isSplit_ofSplit e PQ.1 PQ.2⟩
  left_inv P := Subtype.ext (Pairing.ofSplit_splitLeft_splitRight e P.2)
  right_inv PQ := by
    obtain ⟨P, Q⟩ := PQ
    simp only [Prod.mk.injEq]
    exact ⟨Pairing.splitLeft_ofSplit e P Q, Pairing.splitRight_ofSplit e P Q⟩

end Inverse

section Product

variable {R : Type*}

/-- A left-part kernel read in the ambient orientation.

The ambient order need not agree with the left part's own order, so a pair that the left pairing
lists as `(x, y)` may appear ambiently as `(e (inl y), e (inl x))`. Absorbing the choice into the
kernel — rather than constraining the splitting to be monotone — is the same device
`Combinatorics.orientedKernel` uses for the bipartite determinant. -/
def splitLeftKernel (e : PositionSplitting a b n) (pv : Fin (2 * n) → Fin (2 * n) → R)
    (x y : Fin (2 * a)) : R :=
  if e (Sum.inl x) < e (Sum.inl y) then pv (e (Sum.inl x)) (e (Sum.inl y))
  else pv (e (Sum.inl y)) (e (Sum.inl x))

/-- A right-part kernel read in the ambient orientation. -/
def splitRightKernel (e : PositionSplitting a b n) (pv : Fin (2 * n) → Fin (2 * n) → R)
    (x y : Fin (2 * b)) : R :=
  if e (Sum.inr x) < e (Sum.inr y) then pv (e (Sum.inr x)) (e (Sum.inr y))
  else pv (e (Sum.inr y)) (e (Sum.inr x))

theorem splitLeftKernel_comm (e : PositionSplitting a b n)
    (pv : Fin (2 * n) → Fin (2 * n) → R) (x y : Fin (2 * a)) :
    splitLeftKernel e pv x y = splitLeftKernel e pv y x := by
  unfold splitLeftKernel
  rcases lt_trichotomy (e (Sum.inl x)) (e (Sum.inl y)) with hlt | heq | hgt
  · rw [if_pos hlt, if_neg (asymm hlt)]
  · have hxy : x = y := Sum.inl.inj (e.injective heq)
    subst hxy
    rfl
  · rw [if_neg (asymm hgt), if_pos hgt]

theorem splitRightKernel_comm (e : PositionSplitting a b n)
    (pv : Fin (2 * n) → Fin (2 * n) → R) (x y : Fin (2 * b)) :
    splitRightKernel e pv x y = splitRightKernel e pv y x := by
  unfold splitRightKernel
  rcases lt_trichotomy (e (Sum.inr x)) (e (Sum.inr y)) with hlt | heq | hgt
  · rw [if_pos hlt, if_neg (asymm hlt)]
  · have hxy : x = y := Sum.inr.inj (e.injective heq)
    subst hxy
    rfl
  · rw [if_neg (asymm hgt), if_pos hgt]

/-- **A product over the pairs of an assembled pairing splits into the two parts.**

Each factor is read in the ambient orientation, which is what `splitLeftKernel` and
`splitRightKernel` supply. -/
theorem prod_pairs_ofSplit [CommMonoid R] (e : PositionSplitting a b n)
    (P : Pairing a) (Q : Pairing b) (pv : Fin (2 * n) → Fin (2 * n) → R) :
    (∏ pr ∈ (Pairing.ofSplit e P Q).pairs, pv pr.1 pr.2) =
      (∏ pr ∈ P.pairs, splitLeftKernel e pv pr.1 pr.2) *
        (∏ pr ∈ Q.pairs, splitRightKernel e pv pr.1 pr.2) := by
  classical
  rw [Finset.prod_subtype (Pairing.ofSplit e P Q).pairs (fun _ => Iff.rfl)
      (fun pr => pv pr.1 pr.2),
    ← Equiv.prod_comp (splitPairsEquiv e P Q) (fun pr => pv pr.1.1 pr.1.2),
    Fintype.prod_sum_type]
  refine congrArg₂ (· * ·) ?_ ?_
  · rw [Finset.prod_subtype P.pairs (fun _ => Iff.rfl)
      (fun pr => splitLeftKernel e pv pr.1 pr.2)]
    refine Fintype.prod_congr _ _ fun pr => ?_
    change pv (orientPair (e (Sum.inl pr.1.1)) (e (Sum.inl pr.1.2))).1
        (orientPair (e (Sum.inl pr.1.1)) (e (Sum.inl pr.1.2))).2 = _
    unfold orientPair splitLeftKernel
    split_ifs <;> rfl
  · rw [Finset.prod_subtype Q.pairs (fun _ => Iff.rfl)
      (fun pr => splitRightKernel e pv pr.1 pr.2)]
    refine Fintype.prod_congr _ _ fun pr => ?_
    change pv (orientPair (e (Sum.inr pr.1.1)) (e (Sum.inr pr.1.2))).1
        (orientPair (e (Sum.inr pr.1.1)) (e (Sum.inr pr.1.2))).2 = _
    unfold orientPair splitRightKernel
    split_ifs <;> rfl

/-- **A product over the pairs of a split pairing, when the parts are listed in ambient order.**

The monotone case of `prod_pairs_ofSplit`: each pair is already oriented the way the ambient order
lists it, so no orientation correction survives and the factors are the ambient kernel read directly
on each part. -/
theorem prod_pairs_of_isSplit [CommMonoid R] (e : PositionSplitting a b n)
    {P : Pairing n} (h : P.IsSplit e)
    (hL : StrictMono fun i : Fin (2 * a) => e (Sum.inl i))
    (hR : StrictMono fun i : Fin (2 * b) => e (Sum.inr i))
    (pv : Fin (2 * n) → Fin (2 * n) → R) :
    (∏ pr ∈ P.pairs, pv pr.1 pr.2) =
      (∏ pr ∈ (P.splitLeft e h).pairs, pv (e (Sum.inl pr.1)) (e (Sum.inl pr.2))) *
        (∏ pr ∈ (P.splitRight e h).pairs, pv (e (Sum.inr pr.1)) (e (Sum.inr pr.2))) := by
  classical
  conv_lhs => rw [← Pairing.ofSplit_splitLeft_splitRight e h]
  rw [prod_pairs_ofSplit e (P.splitLeft e h) (P.splitRight e h) pv]
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun pr hpr => ?_)
    (Finset.prod_congr rfl fun pr hpr => ?_)
  · obtain ⟨hlt, -⟩ := ((P.splitLeft e h).mem_pairs_iff pr.1 pr.2).1 (by simpa using hpr)
    unfold splitLeftKernel
    rw [if_pos (hL hlt)]
  · obtain ⟨hlt, -⟩ := ((P.splitRight e h).mem_pairs_iff pr.1 pr.2).1 (by simpa using hpr)
    unfold splitRightKernel
    rw [if_pos (hR hlt)]

end Product

section Monotone

/-- **The splitting a subset of positions induces, enumerated monotonically.**

Both parts are listed by increasing ambient position, so each embedding is strictly monotone. That
is what a *value* attached to a pair needs when it depends on the order of its endpoints — the
oriented kernels of `section Product` make a product identity true without it, but they do not make
the parts carry the same quantity the ambient does. -/
noncomputable def monotonePositionSplitting {m a b : ℕ} (A : Finset (Fin (2 * m)))
    (ha : A.card = 2 * a) (hb : Aᶜ.card = 2 * b) : PositionSplitting a b m :=
  ((Equiv.sumCongr (A.orderIsoOfFin ha).toEquiv
      ((Aᶜ).orderIsoOfFin hb).toEquiv).trans
    (Equiv.sumCongr (Equiv.refl (↥A))
      (Equiv.subtypeEquivRight fun _ => Finset.mem_compl))).trans
    (Equiv.sumCompl (· ∈ A))

@[simp]
theorem monotonePositionSplitting_inl {m a b : ℕ} (A : Finset (Fin (2 * m)))
    (ha : A.card = 2 * a) (hb : Aᶜ.card = 2 * b) (i : Fin (2 * a)) :
    monotonePositionSplitting A ha hb (Sum.inl i) = (A.orderIsoOfFin ha i : Fin (2 * m)) := by
  simp [monotonePositionSplitting]

@[simp]
theorem monotonePositionSplitting_inr {m a b : ℕ} (A : Finset (Fin (2 * m)))
    (ha : A.card = 2 * a) (hb : Aᶜ.card = 2 * b) (j : Fin (2 * b)) :
    monotonePositionSplitting A ha hb (Sum.inr j) = ((Aᶜ).orderIsoOfFin hb j : Fin (2 * m)) := by
  simp [monotonePositionSplitting]

/-- The left part is listed in increasing ambient order. -/
theorem strictMono_monotonePositionSplitting_inl {m a b : ℕ} (A : Finset (Fin (2 * m)))
    (ha : A.card = 2 * a) (hb : Aᶜ.card = 2 * b) :
    StrictMono fun i => monotonePositionSplitting A ha hb (Sum.inl i) := by
  intro x y hxy
  simp only [monotonePositionSplitting_inl]
  exact (A.orderIsoOfFin ha).strictMono hxy

/-- The right part is listed in increasing ambient order. -/
theorem strictMono_monotonePositionSplitting_inr {m a b : ℕ} (A : Finset (Fin (2 * m)))
    (ha : A.card = 2 * a) (hb : Aᶜ.card = 2 * b) :
    StrictMono fun j => monotonePositionSplitting A ha hb (Sum.inr j) := by
  intro x y hxy
  simp only [monotonePositionSplitting_inr]
  exact ((Aᶜ).orderIsoOfFin hb).strictMono hxy

end Monotone

section Sign

/-- Regroup the block-slot presentation of `Fin (2 * n)` along a split of its `n` pairs into `a`
pairs and `b` pairs. Each two-element block lands whole in one part. -/
noncomputable def splitBlockEquiv (hab : a + b = n) :
    Fin (2 * n) ≃ Fin (2 * a) ⊕ Fin (2 * b) :=
  (pairSlotIndexEquiv n).trans
    (((Equiv.prodCongr (finSumFinEquiv.trans (finCongr hab)).symm (Equiv.refl (Fin 2))).trans
      (Equiv.sumProdDistrib (Fin a) (Fin b) (Fin 2))).trans
        (Equiv.sumCongr (pairSlotIndexEquiv a).symm (pairSlotIndexEquiv b).symm))

theorem splitBlockEquiv_apply_left (hab : a + b = n) (j : Fin a) (s : Fin 2) :
    splitBlockEquiv hab
        ((pairSlotIndexEquiv n).symm (finCongr hab (finSumFinEquiv (Sum.inl j)), s)) =
      Sum.inl ((pairSlotIndexEquiv a).symm (j, s)) := by
  simp [splitBlockEquiv]

theorem splitBlockEquiv_apply_right (hab : a + b = n) (j : Fin b) (s : Fin 2) :
    splitBlockEquiv hab
        ((pairSlotIndexEquiv n).symm (finCongr hab (finSumFinEquiv (Sum.inr j)), s)) =
      Sum.inr ((pairSlotIndexEquiv b).symm (j, s)) := by
  simp [splitBlockEquiv]

variable (e : PositionSplitting a b n) (hab : a + b = n) {P : Pairing n} (h : P.IsSplit e)

/-- The permutation listing the pairs of a split pairing, the left part's pairs first. -/
noncomputable def splitListingPerm : Equiv.Perm (Fin (2 * n)) :=
  (splitBlockEquiv hab).trans
    ((Equiv.sumCongr (P.splitLeft e h).pairPerm (P.splitRight e h).pairPerm).trans e)

/-- The listing permutation presents the pairing: each of its blocks carries a pair of partners. -/
theorem presentsPairs_splitListingPerm : P.PresentsPairs (splitListingPerm e hab h) := by
  refine P.presentsPairs_of_partner_blockPair _ fun k => ?_
  obtain ⟨y, rfl⟩ := (finSumFinEquiv.trans (finCongr hab)).surjective k
  rw [blockPair_apply]
  cases y with
  | inl j =>
      simp only [splitListingPerm, Equiv.trans_apply, splitBlockEquiv_apply_left,
        Equiv.sumCongr_apply, Sum.map_inl, Pairing.pairPerm_pairSlotIndexEquiv_symm]
      rw [Pairing.partner_splitLeft e h, (P.splitLeft e h).partner_pairSlotEquiv_zero]
  | inr j =>
      simp only [splitListingPerm, Equiv.trans_apply, splitBlockEquiv_apply_right,
        Equiv.sumCongr_apply, Sum.map_inr, Pairing.pairPerm_pairSlotIndexEquiv_symm]
      rw [Pairing.partner_splitRight e h, (P.splitRight e h).partner_pairSlotEquiv_zero]

/-- No block of the listing permutation is reversed, when each part is embedded in increasing
order. -/
theorem splitListingPerm_no_reversed_block
    (hL : StrictMono fun i : Fin (2 * a) => e (Sum.inl i))
    (hR : StrictMono fun i : Fin (2 * b) => e (Sum.inr i)) (k : Fin n) :
    ¬ (blockPair (splitListingPerm e hab h) k).2 < (blockPair (splitListingPerm e hab h) k).1 := by
  obtain ⟨y, rfl⟩ := (finSumFinEquiv.trans (finCongr hab)).surjective k
  rw [blockPair_apply]
  cases y with
  | inl j =>
      simp only [splitListingPerm, Equiv.trans_apply, splitBlockEquiv_apply_left,
        Equiv.sumCongr_apply, Sum.map_inl, Pairing.pairPerm_pairSlotIndexEquiv_symm]
      exact asymm (hL ((P.splitLeft e h).pairSlotEquiv_zero_lt_one j))
  | inr j =>
      simp only [splitListingPerm, Equiv.trans_apply, splitBlockEquiv_apply_right,
        Equiv.sumCongr_apply, Sum.map_inr, Pairing.pairPerm_pairSlotIndexEquiv_symm]
      exact asymm (hR ((P.splitRight e h).pairSlotEquiv_zero_lt_one j))

/-- **Crossing parity factors along a split.** The crossing weight of a pairing none of whose pairs
joins the two parts is the product of the two parts' crossing weights, up to the sign of the
permutation that interleaves the parts — which depends only on the splitting, not on the pairing. -/
theorem neg_one_pow_crossingCount_eq_of_isSplit
    (hL : StrictMono fun i : Fin (2 * a) => e (Sum.inl i))
    (hR : StrictMono fun i : Fin (2 * b) => e (Sum.inr i)) :
    (-1 : ℤˣ) ^ P.crossingCount =
      Equiv.Perm.sign ((splitBlockEquiv hab).trans e) *
        ((-1) ^ (P.splitLeft e h).crossingCount * (-1) ^ (P.splitRight e h).crossingCount) := by
  classical
  have hsign := P.sign_eq_of_presentsPairs (splitListingPerm e hab h)
    (presentsPairs_splitListingPerm e hab h)
  have hzero : (∑ k : Fin n, if (blockPair (splitListingPerm e hab h) k).2 <
      (blockPair (splitListingPerm e hab h) k).1 then 1 else 0) = 0 :=
    Finset.sum_eq_zero fun k _ => if_neg (splitListingPerm_no_reversed_block e hab h hL hR k)
  rw [hzero, pow_zero, one_mul] at hsign
  rw [← hsign, splitListingPerm, sign_trans_sumCongr_trans, Pairing.sign_pairPerm,
    Pairing.sign_pairPerm]

end Sign

end Combinatorics
