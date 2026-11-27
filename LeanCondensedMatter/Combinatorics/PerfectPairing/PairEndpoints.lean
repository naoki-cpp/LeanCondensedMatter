import LeanCondensedMatter.Combinatorics.PerfectPairing.Core

set_option linter.style.header false

/-!
# Endpoints of normalized pairs

Every position of a perfect pairing occurs exactly once among the two endpoints of its normalized
pairs. This file packages that fact as an explicit equivalence, used to reindex sums over
pair-of-pair endpoint comparisons as sums over the ambient paired positions.
-/

namespace Combinatorics

/-- A normalized pair belonging to a fixed pairing. -/
abbrev PairingOn.NormalizedPair {α : Type*} [Fintype α] [LinearOrder α]
    (pairing : PairingOn α) :=
  {pair : α × α // pair ∈ pairing.pairs}

/-- The product over the normalized-pair type equals the product over the underlying finset. -/
theorem PairingOn.prod_normalizedPair_eq_prod_pairs {α R : Type*}
    [Fintype α] [LinearOrder α] [CommMonoid R] (pairing : PairingOn α)
    (value : α → α → R) :
    (∏ pr : pairing.NormalizedPair, value pr.1.1 pr.1.2) =
      ∏ pr ∈ pairing.pairs, value pr.1 pr.2 :=
  (Finset.prod_subtype pairing.pairs (fun _ => Iff.rfl)
    (fun pr => value pr.1 pr.2)).symm

/-- Reindex the product over a pairing's normalized pairs through any finite presentation
of those pairs, using the corresponding local values. -/
theorem PairingOn.prod_pairs_eq_prod_of_equiv {α A R : Type*}
    [Fintype α] [LinearOrder α] [Fintype A] [CommMonoid R] (pairing : PairingOn α)
    (e : A ≃ pairing.NormalizedPair) (value : α → α → R)
    (f : A → R) (hvalue : ∀ a, value (e a).1.1 (e a).1.2 = f a) :
    (∏ pr ∈ pairing.pairs, value pr.1 pr.2) = ∏ a, f a := by
  classical
  calc
    _ = ∏ pr : pairing.NormalizedPair, value pr.1.1 pr.1.2 :=
      (pairing.prod_normalizedPair_eq_prod_pairs value).symm
    _ = ∏ a : A, value (e a).1.1 (e a).1.2 :=
      (Equiv.prod_comp e (fun pr => value pr.1.1 pr.1.2)).symm
    _ = _ := by
      apply Fintype.prod_congr
      exact hvalue

/-- Select endpoint `0` or endpoint `1` of an ordered pair. -/
def pairEndpointAt {α : Type*} (pair : α × α) (k : Fin 2) : α :=
  if k = 0 then pair.1 else pair.2

@[simp]
theorem pairEndpointAt_zero {α : Type*} (p : α × α) :
    pairEndpointAt p 0 = p.1 := by
  simp [pairEndpointAt]

@[simp]
theorem pairEndpointAt_one {α : Type*} (p : α × α) :
    pairEndpointAt p 1 = p.2 := by
  simp [pairEndpointAt]

/-- The two endpoints of all normalized pairs are equivalent to the ambient paired positions. -/
noncomputable def PairingOn.pairEndpointEquiv {α : Type*} [Fintype α] [LinearOrder α]
    (pairing : PairingOn α) : pairing.NormalizedPair × Fin 2 ≃ α := by
  classical
  let inverse : α → pairing.NormalizedPair × Fin 2 := fun i => by
    by_cases h : i < pairing.partner i
    · exact (⟨(i, pairing.partner i),
        (pairing.mem_pairs_iff i (pairing.partner i)).2 ⟨h, rfl⟩⟩, 0)
    · exact (⟨(pairing.partner i, i),
        (pairing.mem_pairs_iff (pairing.partner i) i).2
          ⟨lt_of_le_of_ne (le_of_not_gt h) (pairing.partner_ne i),
            pairing.partner_partner i⟩⟩, 1)
  refine
    { toFun := fun x => pairEndpointAt x.1.1 x.2
      invFun := inverse
      left_inv := ?_
      right_inv := ?_ }
  · rintro ⟨⟨⟨a, b⟩, hab⟩, k⟩
    have hpair := (pairing.mem_pairs_iff a b).1 hab
    have hablt : a < b := hpair.1
    have hpartnera : pairing.partner a = b := hpair.2
    have hpartnerb : pairing.partner b = a := by
      rw [← hpartnera, pairing.partner_partner]
    fin_cases k
    · simp [inverse, pairEndpointAt, hablt, hpartnera]
    · have hba : ¬ b < a := not_lt_of_ge (le_of_lt hablt)
      simp [inverse, pairEndpointAt, hba, hpartnerb]
  · intro i
    by_cases h : i < pairing.partner i
    · simp [inverse, pairEndpointAt, h]
    · simp [inverse, pairEndpointAt, h]

@[simp]
theorem PairingOn.pairEndpointEquiv_apply {α : Type*} [Fintype α] [LinearOrder α]
    (pairing : PairingOn α)
    (x : pairing.NormalizedPair × Fin 2) :
    pairing.pairEndpointEquiv x = pairEndpointAt x.1.1 x.2 :=
  rfl

/-- The normalized endpoint equivalence counts each pair exactly twice. -/
theorem PairingOn.card_eq_two_mul_card_normalizedPair {α : Type*} [Fintype α] [LinearOrder α]
    (pairing : PairingOn α) : Fintype.card α = 2 * Fintype.card pairing.NormalizedPair := by
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.mul_comm] using
    (Fintype.card_congr pairing.pairEndpointEquiv).symm

/-- Counting the `2 * n` ambient positions two at a time: a perfect pairing of `Fin (2 * n)` has
exactly `n` normalized pairs. -/
theorem Pairing.card_normalizedPair {n : ℕ} (pairing : Pairing n) :
    Fintype.card pairing.NormalizedPair = n := by
  have h := pairing.card_eq_two_mul_card_normalizedPair
  simp only [Fintype.card_fin] at h
  omega

/-- Normalize endpoint zero after transporting an abstract two-endpoint fiber into `pairing`. -/
noncomputable def PairingOn.normalizedPairOfEndpointEquiv
    {A P α : Type*} [Fintype α] [LinearOrder α] (pairing : PairingOn α)
    (endpointEquiv : A × Fin 2 ≃ P) (e : P ≃ α) :
    A → pairing.NormalizedPair :=
  fun a => (pairing.pairEndpointEquiv.symm (e (endpointEquiv (a, 0)))).1

/-- Normalizing a transported endpoint-zero position preserves the two source endpoints up to the
normalized order chosen by the target pairing. -/
theorem PairingOn.normalizedPairOfEndpointEquiv_pair_eq_or_swap
    {A P α : Type*} [Fintype α] [LinearOrder α] (pairing : PairingOn α)
    (endpointEquiv : A × Fin 2 ≃ P) (e : P ≃ α)
    (hpartner : ∀ a : A,
      pairing.partner (e (endpointEquiv (a, 0))) = e (endpointEquiv (a, 1)))
    (a : A) :
    (pairing.normalizedPairOfEndpointEquiv endpointEquiv e a).1 =
        (e (endpointEquiv (a, 0)), e (endpointEquiv (a, 1))) ∨
      (pairing.normalizedPairOfEndpointEquiv endpointEquiv e a).1 =
        (e (endpointEquiv (a, 1)), e (endpointEquiv (a, 0))) := by
  classical
  unfold PairingOn.normalizedPairOfEndpointEquiv
  by_cases horder : e (endpointEquiv (a, 0)) < e (endpointEquiv (a, 1))
  · left
    simp [PairingOn.pairEndpointEquiv, hpartner a, horder]
  · right
    simp [PairingOn.pairEndpointEquiv, hpartner a, horder]

/-- Transport an abstract family of paired endpoint fibers to the normalized pairs of `pairing`.

The source type `A` need not itself be a `Pairing`. The endpoint equivalences exhaust the ambient
positions, and the partner of transported endpoint zero is transported endpoint one. The inverse
reads the source pair index of the first normalized endpoint. -/
noncomputable def PairingOn.normalizedPairEquivOfEndpointEquiv
    {A P α : Type*} [Fintype α] [LinearOrder α] (pairing : PairingOn α)
    (endpointEquiv : A × Fin 2 ≃ P) (e : P ≃ α)
    (hpartner : ∀ a : A,
      pairing.partner (e (endpointEquiv (a, 0))) = e (endpointEquiv (a, 1))) :
    A ≃ pairing.NormalizedPair := by
  let E := endpointEquiv.trans e
  refine {
    toFun := pairing.normalizedPairOfEndpointEquiv endpointEquiv e
    invFun := fun pr => (E.symm pr.1.1).1
    left_inv := ?_
    right_inv := ?_ }
  · intro a
    change (E.symm (pairing.normalizedPairOfEndpointEquiv endpointEquiv e a).1.1).1 = a
    rcases pairing.normalizedPairOfEndpointEquiv_pair_eq_or_swap
        endpointEquiv e hpartner a with h | h
    · rw [congrArg Prod.fst h]
      change (E.symm (E (a, 0))).1 = a
      rw [Equiv.symm_apply_apply]
    · rw [congrArg Prod.fst h]
      change (E.symm (E (a, 1))).1 = a
      rw [Equiv.symm_apply_apply]
  · intro pr
    obtain ⟨⟨a, k⟩, hk⟩ := E.surjective pr.1.1
    change pairing.normalizedPairOfEndpointEquiv endpointEquiv e (E.symm pr.1.1).1 = pr
    rw [← hk, Equiv.symm_apply_apply]
    change (pairing.pairEndpointEquiv.symm (E (a, 0))).1 = pr
    fin_cases k
    · change E (a, 0) = pr.1.1 at hk
      rw [hk]
      exact congrArg Prod.fst (pairing.pairEndpointEquiv.left_inv (pr, 0))
    · change E (a, 1) = pr.1.1 at hk
      have hp : pairing.partner (E (a, 0)) = E (a, 1) := hpartner a
      have hfirst : E (a, 0) = pr.1.2 := by
        calc
          E (a, 0) = pairing.partner (E (a, 1)) := by rw [← hp, pairing.partner_partner]
          _ = pr.1.2 := by
            rw [hk]
            exact ((pairing.mem_pairs_iff pr.1.1 pr.1.2).1 pr.2).2
      rw [hfirst]
      exact congrArg Prod.fst (pairing.pairEndpointEquiv.left_inv (pr, 1))

/-- A partner-intertwining map sends the endpoints of a normalized pair to partnered positions. -/
theorem PairingOn.partner_map_normalizedPair {α β : Type*} [Fintype α] [LinearOrder α]
    (source : PairingOn α) (target : PairingOn β) (f : α → β)
    (hpartner : ∀ i, target.partner (f i) = f (source.partner i))
    (pr : source.NormalizedPair) : target.partner (f pr.1.1) = f pr.1.2 := by
  rw [hpartner, ((source.mem_pairs_iff pr.1.1 pr.1.2).1 pr.2).2]

/-- A partner-intertwining equivalence of positions induces an equivalence of normalized pairs.
The order of pair endpoints may be reversed by the position map. -/
noncomputable def PairingOn.normalizedPairEquivOfPartnerEquiv
    {α β : Type*} [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β]
    (source : PairingOn α) (target : PairingOn β) (e : α ≃ β)
    (hpartner : ∀ p, target.partner (e p) = e (source.partner p)) :
    source.NormalizedPair ≃ target.NormalizedPair :=
  target.normalizedPairEquivOfEndpointEquiv source.pairEndpointEquiv e
    (source.partner_map_normalizedPair target e hpartner)

/-- If the transported endpoint order is already increasing, normalization does not swap the two
endpoints. -/
theorem PairingOn.normalizedPairOfEndpointEquiv_pair_eq_of_lt
    {A P α : Type*} [Fintype α] [LinearOrder α] (pairing : PairingOn α)
    (endpointEquiv : A × Fin 2 ≃ P) (e : P ≃ α)
    (hpartner : ∀ a : A,
      pairing.partner (e (endpointEquiv (a, 0))) = e (endpointEquiv (a, 1)))
    (a : A)
    (horder : e (endpointEquiv (a, 0)) < e (endpointEquiv (a, 1))) :
    (pairing.normalizedPairOfEndpointEquiv endpointEquiv e a).1 =
      (e (endpointEquiv (a, 0)), e (endpointEquiv (a, 1))) := by
  rcases pairing.normalizedPairOfEndpointEquiv_pair_eq_or_swap
      endpointEquiv e hpartner a with h | h
  · exact h
  · have hnormalized := pairing.pairs_normalized
      (pairing.normalizedPairOfEndpointEquiv endpointEquiv e a).2
    rw [h] at hnormalized
    exact (lt_asymm horder hnormalized).elim

/-- An order-preserving equivalence of paired positions transports each
**normalized pair with its two endpoints in their original order**.
Unlike a general partner-intertwining equivalence, no endpoint swap is
needed. This is the common bridge for crossing-sign and oriented-kernel
preservation. -/
theorem PairingOn.normalizedPairEquivOfPartnerEquiv_apply_of_strictMono
    {α β : Type*} [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β]
    (source : PairingOn α) (target : PairingOn β) (e : α ≃ β)
    (hpartner : ∀ p, target.partner (e p) = e (source.partner p))
    (hmono : StrictMono e) (pr : source.NormalizedPair) :
    (source.normalizedPairEquivOfPartnerEquiv target e hpartner pr).1 =
      (e pr.1.1, e pr.1.2) := by
  change
    (target.normalizedPairOfEndpointEquiv source.pairEndpointEquiv e pr).1 =
      (e pr.1.1, e pr.1.2)
  exact target.normalizedPairOfEndpointEquiv_pair_eq_of_lt
    source.pairEndpointEquiv e (source.partner_map_normalizedPair target e hpartner) pr
    (hmono (source.pairs_normalized pr.2))

/-- Endpoints selected from distinct normalized pairs are distinct. -/
theorem PairingOn.pairEndpoint_ne_of_normalizedPair_ne {α : Type*} [Fintype α] [LinearOrder α] (pairing : PairingOn α)
    (p q : pairing.NormalizedPair) (hpq : p ≠ q) (i j : Fin 2) :
    pairEndpointAt p.1 i ≠ pairEndpointAt q.1 j := by
  intro h
  have hargs : (p, i) = (q, j) :=
    pairing.pairEndpointEquiv.injective (by
      simpa only [pairing.pairEndpointEquiv_apply] using h)
  exact hpq (congrArg Prod.fst hargs)

/-- Distinct normalized pairs in one pairing cannot share an endpoint. -/
theorem PairingOn.normalizedPair_endpoints_ne_of_ne {α : Type*} [Fintype α] [LinearOrder α] (pairing : PairingOn α)
    (p q : pairing.NormalizedPair) (hpq : p ≠ q) :
    p.1.1 ≠ q.1.1 ∧ p.1.1 ≠ q.1.2 ∧ p.1.2 ≠ q.1.1 ∧ p.1.2 ≠ q.1.2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using pairing.pairEndpoint_ne_of_normalizedPair_ne p q hpq (0 : Fin 2) (0 : Fin 2)
  · simpa using pairing.pairEndpoint_ne_of_normalizedPair_ne p q hpq (0 : Fin 2) (1 : Fin 2)
  · simpa using pairing.pairEndpoint_ne_of_normalizedPair_ne p q hpq (1 : Fin 2) (0 : Fin 2)
  · simpa using pairing.pairEndpoint_ne_of_normalizedPair_ne p q hpq (1 : Fin 2) (1 : Fin 2)

end Combinatorics
