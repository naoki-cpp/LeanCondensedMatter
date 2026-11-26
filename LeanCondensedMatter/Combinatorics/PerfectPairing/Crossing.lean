import LeanCondensedMatter.Combinatorics.PerfectPairing.PairEndpoints

set_option linter.style.header false

/-!
# Crossings and crossing counts

Two normalized pairs `(a, b)` and `(c, d)` cross when `a < c < b < d`. The canonical public
crossing representation uses `PairingOn.NormalizedPair`, but the crossing relation itself only
requires an order on the endpoint type.
-/

namespace Combinatorics

/-- The normalized pair `(a, b)` crosses `(c, d)` when `a < c < b < d`. -/
def Crosses {α : Type*} [LT α] (left right : α × α) : Prop :=
  left.1 < right.1 ∧ right.1 < left.2 ∧ left.2 < right.2

instance decidableCrosses {α : Type*} [LT α] [DecidableLT α]
    (left right : α × α) : Decidable (Crosses left right) :=
  inferInstanceAs (Decidable (
    left.1 < right.1 ∧ right.1 < left.2 ∧ left.2 < right.2))

/-- The two oriented crossing indicators are disjoint, so their sum counts geometric crossings
without double counting. -/
theorem crossesIndicator_add {α : Type*} [Preorder α] [DecidableLT α]
    (left right : α × α) :
    (if Crosses left right then (1 : ℕ) else 0) +
      (if Crosses right left then 1 else 0) =
        (if Crosses left right ∨ Crosses right left then 1 else 0) := by
  by_cases hleft : Crosses left right
  · have hright : ¬ Crosses right left := fun h => lt_asymm hleft.1 h.1
    simp [hleft, hright]
  · simp [hleft]

/-- A strictly monotone embedding preserves and reflects the crossing relation. -/
theorem crosses_map_iff {α β : Type*} [LinearOrder α] [Preorder β]
    (f : α → β) (hf : StrictMono f) (a b c e : α) :
    Crosses (f a, f b) (f c, f e) ↔ Crosses (a, b) (c, e) := by
  simp only [Crosses, hf.lt_iff_lt]

/-- A crossing-preserving equivalence of finite pair families preserves the double crossing count. -/
theorem sum_sum_crosses_eq_of_equiv {α β A B : Type*}
    [LT α] [DecidableLT α] [LT β] [DecidableLT β] [Fintype A] [Fintype B]
    (pairA : A → α × α) (pairB : B → β × β)
    (e : A ≃ B)
    (hcross : ∀ p q, Crosses (pairA p) (pairA q) ↔
      Crosses (pairB (e p)) (pairB (e q))) :
    (∑ p : A, ∑ q : A, if Crosses (pairA p) (pairA q) then 1 else 0) =
      ∑ p : B, ∑ q : B, if Crosses (pairB p) (pairB q) then 1 else 0 := by
  classical
  refine Fintype.sum_equiv e
    (fun p : A => ∑ q : A, if Crosses (pairA p) (pairA q) then 1 else 0)
    (fun p : B => ∑ q : B, if Crosses (pairB p) (pairB q) then 1 else 0) ?_
  intro p
  refine Fintype.sum_equiv e
    (fun q : A => if Crosses (pairA p) (pairA q) then 1 else 0)
    (fun q : B => if Crosses (pairB (e p)) (pairB q) then 1 else 0) ?_
  intro q
  exact if_congr (hcross p q) rfl rfl

/-- The number of geometric crossings. -/
def PairingOn.crossingCount {α : Type*} [Fintype α] [LinearOrder α] (pairing : PairingOn α) : ℕ :=
  ((pairing.pairs.product pairing.pairs).filter fun pairPair =>
    Crosses pairPair.1 pairPair.2).card

/-- `crossingCount` as a `0`-or-`1` sum over all ordered normalized-pair pairs. -/
theorem PairingOn.crossingCount_eq_sum_crosses {α : Type*} [Fintype α] [LinearOrder α]
    (pairing : PairingOn α) :
    pairing.crossingCount =
      ∑ x : pairing.NormalizedPair × pairing.NormalizedPair,
        if Crosses x.1.1 x.2.1 then 1 else 0 := by
  classical
  calc
    pairing.crossingCount =
        ∑ x ∈ pairing.pairs.product pairing.pairs,
          if Crosses x.1 x.2 then 1 else 0 := by
      simpa [PairingOn.crossingCount] using
        (Finset.sum_boole (R := ℕ)
          (fun x : (α × α) × (α × α) =>
            Crosses x.1 x.2) (pairing.pairs.product pairing.pairs)).symm
    _ = ∑ p ∈ pairing.pairs, ∑ q ∈ pairing.pairs,
          if Crosses p q then 1 else 0 := by
      exact Finset.sum_product' pairing.pairs pairing.pairs
        (fun p q => if Crosses p q then (1 : ℕ) else 0)
    _ = ∑ p ∈ pairing.pairs.attach, ∑ q ∈ pairing.pairs.attach,
          if Crosses p.1 q.1 then 1 else 0 := by
      calc
        (∑ p ∈ pairing.pairs, ∑ q ∈ pairing.pairs,
          if Crosses p q then 1 else 0) =
            ∑ p ∈ pairing.pairs.attach, ∑ q ∈ pairing.pairs,
              if Crosses p.1 q then 1 else 0 :=
          (Finset.sum_attach pairing.pairs
            (fun p => ∑ q ∈ pairing.pairs, if Crosses p q then (1 : ℕ) else 0)).symm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro p _
          exact (Finset.sum_attach pairing.pairs
            (fun q => if Crosses p.1 q then (1 : ℕ) else 0)).symm
    _ = _ := by
      simp only [Finset.attach_eq_univ, Fintype.sum_prod_type]

/-- Reindex the double crossing sum through a finite presentation of a pairing's normalized
pairs whose endpoints are mapped by a strictly increasing position map. -/
theorem PairingOn.sum_sum_crosses_map_eq_crossingCount
    {α β A : Type*} [Fintype α] [LinearOrder α] [LinearOrder β] [Fintype A]
    (pairing : PairingOn α) (f : α → β) (hmono : StrictMono f)
    (pairImage : A → β × β) (e : A ≃ pairing.NormalizedPair)
    (himage : ∀ p, pairImage p = (f (e p).1.1, f (e p).1.2)) :
    (∑ p : A, ∑ q : A, if Crosses (pairImage p) (pairImage q) then 1 else 0) =
      pairing.crossingCount := by
  rw [pairing.crossingCount_eq_sum_crosses, Fintype.sum_prod_type]
  exact sum_sum_crosses_eq_of_equiv pairImage (fun p : pairing.NormalizedPair => p.1)
    e (fun p q => by
      rw [himage p, himage q]
      exact crosses_map_iff f hmono (e p).1.1 (e p).1.2 (e q).1.1 (e q).1.2)

/-- Summing both crossing orientations over two finite families counts each geometric crossing
once, without any disjointness or normalization assumption on the families. -/
theorem sum_sum_crosses_oriented_add {α A B : Type*}
    [Preorder α] [DecidableLT α] [Fintype A] [Fintype B]
    (left : A → α × α) (right : B → α × α) :
    (∑ p : A, ∑ q : B, if Crosses (left p) (right q) then 1 else 0) +
      (∑ q : B, ∑ p : A, if Crosses (right q) (left p) then 1 else 0) =
      ∑ x : A × B, if Crosses (left x.1) (right x.2) ∨
        Crosses (right x.2) (left x.1) then 1 else 0 := by
  classical
  rw [Fintype.sum_prod_type,
    Finset.sum_comm (f := fun q : B => fun p : A =>
      if Crosses (right q) (left p) then (1 : ℕ) else 0),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun q _ => crossesIndicator_add _ _

/-- Merely changing the natural-number index of a finite perfect
pairing by equality leaves its geometric crossing count unchanged.  In
particular, casting the pair count during canonical interaction-slot
standardization introduces no extra fermionic crossing sign. -/
theorem Pairing.cast_crossingCount {m n : ℕ} (h : m = n)
    (pairing : Pairing m) :
    (Equiv.cast (congrArg Pairing h) pairing).crossingCount =
      pairing.crossingCount := by
  cases h
  rfl

/-- An order-preserving equivalence that intertwines the **actual**
perfect-pairing partners preserves the geometric crossing count exactly.
The induced map on normalized pairs cannot exchange their endpoints,
so the proof does not assume any symmetry of oriented contractions. -/
theorem PairingOn.crossingCount_eq_of_partnerEquiv_strictMono
    {α β : Type*} [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β]
    (source : PairingOn α) (target : PairingOn β) (e : α ≃ β)
    (hpartner : ∀ p, target.partner (e p) = e (source.partner p))
    (hmono : StrictMono e) :
    source.crossingCount = target.crossingCount := by
  let pairEquiv := source.normalizedPairEquivOfPartnerEquiv target e hpartner
  have hpair (pr : source.NormalizedPair) :
      (pairEquiv pr).1 = (e pr.1.1, e pr.1.2) :=
    source.normalizedPairEquivOfPartnerEquiv_apply_of_strictMono
      target e hpartner hmono pr
  rw [target.crossingCount_eq_sum_crosses, Fintype.sum_prod_type]
  exact (source.sum_sum_crosses_map_eq_crossingCount e hmono
    (fun p : target.NormalizedPair => p.1) pairEquiv.symm
    (fun p => by simpa only [Equiv.apply_symm_apply] using hpair (pairEquiv.symm p))).symm

/-- The number of pairs crossing `firstPair`. -/
def Pairing.crossingsWithFirstPair {n : ℕ} (pairing : Pairing (n + 1)) : ℕ :=
  (pairing.pairs.filter fun p => Crosses pairing.firstPair p).card

theorem not_crosses_self {α : Type*} [Preorder α] (p : α × α) : ¬ Crosses p p := by
  rintro ⟨h, -, -⟩
  exact absurd h (lt_irrefl _)

end Combinatorics
