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

/-- Recover the normalized pair and endpoint index containing a position. -/
noncomputable def Pairing.positionToPairEndpoint {n : ℕ} (pairing : Pairing n) :
    Fin (2 * n) → pairing.NormalizedPair × Fin 2 := by
  classical
  intro i
  by_cases h : i < pairing.partner i
  · exact (⟨(i, pairing.partner i),
      (pairing.mem_pairs_iff i (pairing.partner i)).2 ⟨h, rfl⟩⟩, 0)
  · exact (⟨(pairing.partner i, i),
      (pairing.mem_pairs_iff (pairing.partner i) i).2
        ⟨lt_of_le_of_ne (le_of_not_gt h) (pairing.partner_ne i),
          pairing.partner_partner i⟩⟩, 1)

/-- The two endpoints of all normalized pairs are equivalent to the ambient paired positions. -/
noncomputable def Pairing.pairEndpointEquiv {n : ℕ} (pairing : Pairing n) :
    pairing.NormalizedPair × Fin 2 ≃ Fin (2 * n) where
  toFun := pairing.pairEndpoint
  invFun := pairing.positionToPairEndpoint
  left_inv := by
    rintro ⟨⟨⟨a, b⟩, hab⟩, k⟩
    have hpair := (pairing.mem_pairs_iff a b).1 hab
    have hablt : a < b := hpair.1
    have hpartnera : pairing.partner a = b := hpair.2
    have hpartnerb : pairing.partner b = a := by
      rw [← hpartnera, pairing.partner_partner]
    fin_cases k
    · simp [Pairing.pairEndpoint, Pairing.positionToPairEndpoint, hablt, hpartnera]
    · have hba : ¬ b < a := not_lt_of_ge (le_of_lt hablt)
      simp [Pairing.pairEndpoint, Pairing.positionToPairEndpoint, hba, hpartnerb]
  right_inv := by
    intro i
    by_cases h : i < pairing.partner i
    · simp [Pairing.pairEndpoint, Pairing.positionToPairEndpoint, h]
    · simp [Pairing.pairEndpoint, Pairing.positionToPairEndpoint, h]

@[simp]
theorem Pairing.pairEndpointEquiv_apply {n : ℕ} (pairing : Pairing n)
    (x : pairing.NormalizedPair × Fin 2) :
    pairing.pairEndpointEquiv x = pairing.pairEndpoint x :=
  rfl

/-- Recovering the normalized pair from either of its selected endpoints returns that pair. -/
@[simp]
theorem Pairing.positionToPairEndpoint_fst_pairEndpoint {n : ℕ}
    (pairing : Pairing n) (pr : pairing.NormalizedPair) (k : Fin 2) :
    (pairing.positionToPairEndpoint (pairing.pairEndpoint (pr, k))).1 = pr :=
  congrArg Prod.fst (pairing.pairEndpointEquiv.left_inv (pr, k))

/-- Transport an abstract family of paired endpoint fibers to the normalized pairs of `pairing`.

The source type `A` need not itself be a `Pairing`. It is enough to know that every source object has
two endpoints, that these endpoints exhaust a finite position fiber `P`, and that after transporting
`P` to the ambient positions of `pairing`, the partner of endpoint zero is endpoint one. -/
noncomputable def Pairing.normalizedPairEquivOfEndpointEquiv
    {A P : Type*} [Fintype A] [Finite P] {n : ℕ} (pairing : Pairing n)
    (endpointEquiv : A × Fin 2 ≃ P) (e : P ≃ Fin (2 * n))
    (hpartner : ∀ a : A,
      pairing.partner (e (endpointEquiv (a, 0))) = e (endpointEquiv (a, 1))) :
    A ≃ pairing.NormalizedPair := by
  let transport : A → pairing.NormalizedPair := fun a =>
    (pairing.positionToPairEndpoint (e (endpointEquiv (a, 0)))).1
  have hsurj : Function.Surjective transport := by
    intro localPr
    let p : P := e.symm localPr.1.1
    let x : A × Fin 2 := endpointEquiv.symm p
    refine ⟨x.1, ?_⟩
    have hx : endpointEquiv x = p := endpointEquiv.apply_symm_apply p
    rcases x with ⟨a, k⟩
    fin_cases k
    · have hfirst : e (endpointEquiv (a, 0)) = localPr.1.1 := by
        calc
          e (endpointEquiv (a, 0)) = e p := congrArg e (by simpa using hx)
          _ = localPr.1.1 := e.apply_symm_apply localPr.1.1
      change (pairing.positionToPairEndpoint (e (endpointEquiv (a, 0)))).1 = localPr
      rw [hfirst]
      simpa using pairing.positionToPairEndpoint_fst_pairEndpoint localPr 0
    · have hsecond : e (endpointEquiv (a, 1)) = localPr.1.1 := by
        calc
          e (endpointEquiv (a, 1)) = e p := congrArg e (by simpa using hx)
          _ = localPr.1.1 := e.apply_symm_apply localPr.1.1
      have hlocalPartner : pairing.partner (e (endpointEquiv (a, 0))) = localPr.1.1 := by
        rw [hpartner a, hsecond]
      have hpair := (pairing.mem_pairs_iff localPr.1.1 localPr.1.2).1 localPr.2
      have hfirst : e (endpointEquiv (a, 0)) = localPr.1.2 := by
        calc
          e (endpointEquiv (a, 0)) =
              pairing.partner (pairing.partner (e (endpointEquiv (a, 0)))) := by
            rw [pairing.partner_partner]
          _ = pairing.partner localPr.1.1 := by rw [hlocalPartner]
          _ = localPr.1.2 := hpair.2
      change (pairing.positionToPairEndpoint (e (endpointEquiv (a, 0)))).1 = localPr
      rw [hfirst]
      simpa using pairing.positionToPairEndpoint_fst_pairEndpoint localPr 1
  have hcard : Fintype.card A = Fintype.card pairing.NormalizedPair := by
    letI : Fintype P := Fintype.ofFinite P
    have h : Fintype.card (A × Fin 2) =
        Fintype.card (pairing.NormalizedPair × Fin 2) :=
      (Fintype.card_congr endpointEquiv).trans
        ((Fintype.card_congr e).trans
          (Fintype.card_congr pairing.pairEndpointEquiv).symm)
    simp only [Fintype.card_prod, Fintype.card_fin] at h
    omega
  exact Equiv.ofBijective transport
    ((Fintype.bijective_iff_surjective_and_card _).2 ⟨hsurj, hcard⟩)

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
