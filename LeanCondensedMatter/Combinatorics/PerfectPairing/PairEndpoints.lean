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
abbrev Pairing.NormalizedPair {n : ℕ} (pairing : Pairing n) :=
  {pair : Fin (2 * n) × Fin (2 * n) // pair ∈ pairing.pairs}

/-- Reindex the product over a pairing's normalized pairs through any finite presentation
of those pairs, using the corresponding local values. -/
theorem Pairing.prod_pairs_eq_prod_of_equiv {n : ℕ} {A R : Type*}
    [Fintype A] [CommMonoid R] (pairing : Pairing n)
    (e : A ≃ pairing.NormalizedPair) (value : Fin (2 * n) → Fin (2 * n) → R)
    (f : A → R) (hvalue : ∀ a, value (e a).1.1 (e a).1.2 = f a) :
    (∏ pr ∈ pairing.pairs, value pr.1 pr.2) = ∏ a, f a := by
  classical
  calc
    _ = ∏ pr : pairing.NormalizedPair, value pr.1.1 pr.1.2 :=
      Finset.prod_subtype _ (fun _ => Iff.rfl) _
    _ = ∏ a : A, value (e a).1.1 (e a).1.2 :=
      (Equiv.prod_comp e (fun pr => value pr.1.1 pr.1.2)).symm
    _ = _ := by
      apply Fintype.prod_congr
      exact hvalue

/-- Select endpoint `0` or endpoint `1` of a normalized pair. -/
def Pairing.pairEndpoint {n : ℕ} (pairing : Pairing n) :
    pairing.NormalizedPair × Fin 2 → Fin (2 * n) :=
  fun x => if x.2 = 0 then x.1.1.1 else x.1.1.2

@[simp]
theorem Pairing.pairEndpoint_zero {n : ℕ} (pairing : Pairing n)
    (p : pairing.NormalizedPair) :
    pairing.pairEndpoint (p, 0) = p.1.1 := by
  simp [Pairing.pairEndpoint]

@[simp]
theorem Pairing.pairEndpoint_one {n : ℕ} (pairing : Pairing n)
    (p : pairing.NormalizedPair) :
    pairing.pairEndpoint (p, 1) = p.1.2 := by
  simp [Pairing.pairEndpoint]

/-- The two endpoints of all normalized pairs are equivalent to the ambient paired positions. -/
noncomputable def Pairing.pairEndpointEquiv {n : ℕ} (pairing : Pairing n) :
    pairing.NormalizedPair × Fin 2 ≃ Fin (2 * n) := by
  classical
  let inverse : Fin (2 * n) → pairing.NormalizedPair × Fin 2 := fun i => by
    by_cases h : i < pairing.partner i
    · exact (⟨(i, pairing.partner i),
        (pairing.mem_pairs_iff i (pairing.partner i)).2 ⟨h, rfl⟩⟩, 0)
    · exact (⟨(pairing.partner i, i),
        (pairing.mem_pairs_iff (pairing.partner i) i).2
          ⟨lt_of_le_of_ne (le_of_not_gt h) (pairing.partner_ne i),
            pairing.partner_partner i⟩⟩, 1)
  refine
    { toFun := pairing.pairEndpoint
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
    · simp [inverse, Pairing.pairEndpoint, hablt, hpartnera]
    · have hba : ¬ b < a := not_lt_of_ge (le_of_lt hablt)
      simp [inverse, Pairing.pairEndpoint, hba, hpartnerb]
  · intro i
    by_cases h : i < pairing.partner i
    · simp [inverse, Pairing.pairEndpoint, h]
    · simp [inverse, Pairing.pairEndpoint, h]

@[simp]
theorem Pairing.pairEndpointEquiv_apply {n : ℕ} (pairing : Pairing n)
    (x : pairing.NormalizedPair × Fin 2) :
    pairing.pairEndpointEquiv x = pairing.pairEndpoint x :=
  rfl

/-- Counting the `2 * n` ambient positions two at a time: a perfect pairing of `Fin (2 * n)` has
exactly `n` normalized pairs. -/
theorem Pairing.card_normalizedPair {n : ℕ} (pairing : Pairing n) :
    Fintype.card pairing.NormalizedPair = n := by
  have h : Fintype.card (pairing.NormalizedPair × Fin 2) = Fintype.card (Fin (2 * n)) :=
    Fintype.card_congr pairing.pairEndpointEquiv
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  omega

/-- Normalize endpoint zero after transporting an abstract two-endpoint fiber into `pairing`. -/
noncomputable def Pairing.normalizedPairOfEndpointEquiv
    {A P : Type*} {n : ℕ} (pairing : Pairing n)
    (endpointEquiv : A × Fin 2 ≃ P) (e : P ≃ Fin (2 * n)) :
    A → pairing.NormalizedPair :=
  fun a => (pairing.pairEndpointEquiv.symm (e (endpointEquiv (a, 0)))).1

/-- Normalizing a transported endpoint-zero position preserves the two source endpoints up to the
normalized order chosen by the target pairing. -/
theorem Pairing.normalizedPairOfEndpointEquiv_pair_eq_or_swap
    {A P : Type*} {n : ℕ} (pairing : Pairing n)
    (endpointEquiv : A × Fin 2 ≃ P) (e : P ≃ Fin (2 * n))
    (hpartner : ∀ a : A,
      pairing.partner (e (endpointEquiv (a, 0))) = e (endpointEquiv (a, 1)))
    (a : A) :
    (pairing.normalizedPairOfEndpointEquiv endpointEquiv e a).1 =
        (e (endpointEquiv (a, 0)), e (endpointEquiv (a, 1))) ∨
      (pairing.normalizedPairOfEndpointEquiv endpointEquiv e a).1 =
        (e (endpointEquiv (a, 1)), e (endpointEquiv (a, 0))) := by
  classical
  unfold Pairing.normalizedPairOfEndpointEquiv
  by_cases horder : e (endpointEquiv (a, 0)) < e (endpointEquiv (a, 1))
  · left
    simp [Pairing.pairEndpointEquiv, hpartner a, horder]
  · right
    simp [Pairing.pairEndpointEquiv, hpartner a, horder]

/-- Transport an abstract family of paired endpoint fibers to the normalized pairs of `pairing`.

The source type `A` need not itself be a `Pairing`. The endpoint equivalences exhaust the ambient
positions, and the partner of transported endpoint zero is transported endpoint one. The inverse
reads the source pair index of the first normalized endpoint. -/
noncomputable def Pairing.normalizedPairEquivOfEndpointEquiv
    {A P : Type*} {n : ℕ} (pairing : Pairing n)
    (endpointEquiv : A × Fin 2 ≃ P) (e : P ≃ Fin (2 * n))
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

/-- A partner-intertwining equivalence of positions induces an equivalence of normalized pairs.
The order of pair endpoints may be reversed by the position map. -/
noncomputable def Pairing.normalizedPairEquivOfPartnerEquiv
    {m n : ℕ} (source : Pairing m) (target : Pairing n)
    (e : Fin (2 * m) ≃ Fin (2 * n))
    (hpartner : ∀ p, target.partner (e p) = e (source.partner p)) :
    source.NormalizedPair ≃ target.NormalizedPair :=
  target.normalizedPairEquivOfEndpointEquiv source.pairEndpointEquiv e
    (fun pr => by
      change target.partner (e pr.1.1) = e pr.1.2
      rw [hpartner]
      exact congrArg e (((source.mem_pairs_iff pr.1.1 pr.1.2).1 pr.2).2))

/-- If the transported endpoint order is already increasing, normalization does not swap the two
endpoints. -/
theorem Pairing.normalizedPairOfEndpointEquiv_pair_eq_of_lt
    {A P : Type*} {n : ℕ} (pairing : Pairing n)
    (endpointEquiv : A × Fin 2 ≃ P) (e : P ≃ Fin (2 * n))
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
theorem Pairing.normalizedPairEquivOfPartnerEquiv_apply_of_strictMono
    {m n : ℕ} (source : Pairing m) (target : Pairing n)
    (e : Fin (2 * m) ≃ Fin (2 * n))
    (hpartner : ∀ p, target.partner (e p) = e (source.partner p))
    (hmono : StrictMono e) (pr : source.NormalizedPair) :
    (source.normalizedPairEquivOfPartnerEquiv target e hpartner pr).1 =
      (e pr.1.1, e pr.1.2) := by
  have hpartner0 (q : source.NormalizedPair) :
      target.partner (e (source.pairEndpointEquiv (q, 0))) =
        e (source.pairEndpointEquiv (q, 1)) := by
    change target.partner (e q.1.1) = e q.1.2
    rw [hpartner]
    exact congrArg e (((source.mem_pairs_iff q.1.1 q.1.2).1 q.2).2)
  change
    (target.normalizedPairOfEndpointEquiv source.pairEndpointEquiv e pr).1 =
      (e pr.1.1, e pr.1.2)
  exact target.normalizedPairOfEndpointEquiv_pair_eq_of_lt
    source.pairEndpointEquiv e hpartner0 pr
    (hmono (((source.mem_pairs_iff pr.1.1 pr.1.2).1 pr.2).1))

/-- Endpoints selected from distinct normalized pairs are distinct. -/
theorem Pairing.pairEndpoint_ne_of_normalizedPair_ne {n : ℕ} (pairing : Pairing n)
    (p q : pairing.NormalizedPair) (hpq : p ≠ q) (i j : Fin 2) :
    pairing.pairEndpoint (p, i) ≠ pairing.pairEndpoint (q, j) := by
  intro h
  have hargs : (p, i) = (q, j) :=
    pairing.pairEndpointEquiv.injective (by
      simpa only [pairing.pairEndpointEquiv_apply] using h)
  exact hpq (congrArg Prod.fst hargs)

/-- Distinct normalized pairs in one pairing cannot share an endpoint. -/
theorem Pairing.normalizedPair_endpoints_ne_of_ne {n : ℕ} (pairing : Pairing n)
    (p q : pairing.NormalizedPair) (hpq : p ≠ q) :
    p.1.1 ≠ q.1.1 ∧ p.1.1 ≠ q.1.2 ∧ p.1.2 ≠ q.1.1 ∧ p.1.2 ≠ q.1.2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using pairing.pairEndpoint_ne_of_normalizedPair_ne p q hpq (0 : Fin 2) (0 : Fin 2)
  · simpa using pairing.pairEndpoint_ne_of_normalizedPair_ne p q hpq (0 : Fin 2) (1 : Fin 2)
  · simpa using pairing.pairEndpoint_ne_of_normalizedPair_ne p q hpq (1 : Fin 2) (0 : Fin 2)
  · simpa using pairing.pairEndpoint_ne_of_normalizedPair_ne p q hpq (1 : Fin 2) (1 : Fin 2)

end Combinatorics
