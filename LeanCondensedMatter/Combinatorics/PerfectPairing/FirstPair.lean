import LeanCondensedMatter.Combinatorics.PerfectPairing.Core
import LeanCondensedMatter.Combinatorics.PerfectPairing.PairEndpoints
import LeanCondensedMatter.Combinatorics.PerfectPairing.Restriction
import LeanCondensedMatter.Combinatorics.FiniteIndex.DeletedPositions
import Mathlib.Logic.Equiv.Fin.Basic

set_option linter.style.header false

/-!
# First-pair decomposition

Erasing position zero and its partner and inserting a first pair are inverse operations.
The increasing coordinate map on remaining positions identifies the residual normalized pairs.
The resulting equivalence `Pairing.equivSigma` reindexes finite sums and products without
requiring crossing geometry.
-/

namespace Combinatorics

open FiniteIndex

/-- Remove position `0` and its partner, reindexing the remaining positions increasingly. -/
noncomputable def Pairing.eraseZeroPair {n : ℕ} (pairing : Pairing (n + 1)) : Pairing n := by
  let p := fun i : Fin (2 * (n + 1)) =>
    i ∈ deletedPositions (2 * n) (pairing.partner 0)
  have hpartner : ∀ i, p i ↔ p (pairing.partner i) := by
    intro i
    have hzero : pairing.partner i = 0 ↔ i = pairing.partner 0 :=
      ⟨fun h => by rw [← pairing.partner_partner i, h],
        fun h => by rw [h, pairing.partner_partner]⟩
    have hj : pairing.partner i = pairing.partner 0 ↔ i = 0 :=
      pairing.partner.injective.eq_iff
    simp only [p, deletedPositions, Finset.mem_erase, Finset.mem_univ, and_true,
      ne_eq, hzero, hj]
    exact and_comm
  let e :=
    deletedPositionsOrderIso (2 * n) (pairing.partner 0) (pairing.partner_ne 0)
  exact pairing.restrictAlongEquiv p hpartner e.symm.toEquiv

/-- Increasing equivalence used by `eraseZeroPair`. -/
noncomputable def Pairing.eraseZeroOrderIso {n : ℕ} (pairing : Pairing (n + 1)) :
    Fin (2 * n) ≃o
      deletedPositions (2 * n) (pairing.partner 0) :=
  deletedPositionsOrderIso (2 * n) (pairing.partner 0) (pairing.partner_ne 0)

@[simp]
theorem Pairing.eraseZeroOrderIso_partner {n : ℕ} (pairing : Pairing (n + 1))
    (i : Fin (2 * n)) :
    ((pairing.eraseZeroOrderIso ((pairing.eraseZeroPair).partner i) :
      Fin (2 * (n + 1)))) =
    pairing.partner (pairing.eraseZeroOrderIso i) := by
  simp [Pairing.eraseZeroOrderIso, Pairing.eraseZeroPair, PairingOn.restrictAlongEquiv]

private theorem Pairing.eraseZeroPair_mem_pairs_iff {n : ℕ} (pairing : Pairing (n + 1))
    (i k : Fin (2 * n)) :
    (i, k) ∈ (pairing.eraseZeroPair).pairs ↔
      ((pairing.eraseZeroOrderIso i : Fin (2 * (n + 1))),
        (pairing.eraseZeroOrderIso k : Fin (2 * (n + 1)))) ∈ pairing.pairs := by
  let e : Fin (2 * n) ↪o Fin (2 * (n + 1)) :=
    OrderEmbedding.ofStrictMono (fun i => pairing.eraseZeroOrderIso i)
      (fun _ _ h => pairing.eraseZeroOrderIso.strictMono h)
  exact (pairing.eraseZeroPair.mem_pairs_map_iff pairing e
    (fun i => (pairing.eraseZeroOrderIso_partner i).symm) i k).symm

/-- Every normalized pair other than `firstPair` has both endpoints away from `0` and its
partner. -/
private theorem Pairing.mem_pairs_endpoints_mem_deletedPositions {n : ℕ} (pairing : Pairing (n + 1))
    {p : Fin (2 * (n + 1)) × Fin (2 * (n + 1))} (hp : p ∈ pairing.pairs)
    (hne : p ≠ pairing.firstPair) :
    p.1 ∈ deletedPositions (2 * n) (pairing.partner 0) ∧
      p.2 ∈ deletedPositions (2 * n) (pairing.partner 0) := by
  have hne' : (⟨p, hp⟩ : pairing.NormalizedPair) ≠
      ⟨pairing.firstPair, pairing.firstPair_mem_pairs⟩ :=
    fun h => hne (congrArg Subtype.val h)
  have h := pairing.normalizedPair_endpoints_ne_of_ne _ _ hne'
  change p.1 ≠ 0 ∧ p.1 ≠ pairing.partner 0 ∧
    p.2 ≠ 0 ∧ p.2 ≠ pairing.partner 0 at h
  obtain ⟨h10, h1j, h20, h2j⟩ := h
  simp [deletedPositions, h10, h1j, h20, h2j]

/-- Map a pair of remaining positions to its original ambient positions. -/
noncomputable def Pairing.eraseZeroPairEmbedding {n : ℕ} (pairing : Pairing (n + 1)) :
    (Fin (2 * n) × Fin (2 * n)) ↪
      (Fin (2 * (n + 1)) × Fin (2 * (n + 1))) where
  toFun pr := (pairing.eraseZeroOrderIso pr.1, pairing.eraseZeroOrderIso pr.2)
  inj' := by
    intro p q h
    exact Prod.ext
      (pairing.eraseZeroOrderIso.injective (Subtype.ext (congrArg Prod.fst h)))
      (pairing.eraseZeroOrderIso.injective (Subtype.ext (congrArg Prod.snd h)))

/-- The ambient pairs other than the first pair are exactly the embedded smaller pairing's pairs. -/
theorem Pairing.pairs_erase_firstPair_eq_image {n : ℕ} (pairing : Pairing (n + 1)) :
    pairing.pairs.erase pairing.firstPair =
      pairing.eraseZeroPair.pairs.image pairing.eraseZeroPairEmbedding := by
  classical
  ext p
  simp only [Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro ⟨hne, hp⟩
    obtain ⟨h1, h2⟩ := pairing.mem_pairs_endpoints_mem_deletedPositions hp hne
    refine ⟨(pairing.eraseZeroOrderIso.symm ⟨p.1, h1⟩,
      pairing.eraseZeroOrderIso.symm ⟨p.2, h2⟩), ?_, ?_⟩
    · rw [pairing.eraseZeroPair_mem_pairs_iff]
      simpa using hp
    · change (↑(pairing.eraseZeroOrderIso (pairing.eraseZeroOrderIso.symm ⟨p.1, h1⟩)),
        ↑(pairing.eraseZeroOrderIso (pairing.eraseZeroOrderIso.symm ⟨p.2, h2⟩))) = p
      simp
  · rintro ⟨pr, hpr, rfl⟩
    refine ⟨?_, (pairing.eraseZeroPair_mem_pairs_iff pr.1 pr.2).1 hpr⟩
    intro heq
    have h0 : (pairing.eraseZeroOrderIso pr.1 : Fin (2 * (n + 1))) ≠ 0 :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp (pairing.eraseZeroOrderIso pr.1).property).2).1
    exact h0 (congrArg Prod.fst heq)

/-- The pairing on a two-element type. -/
private def boolPairing : PairingOn Bool :=
  PairingOn.ofPartner (Equiv.swap false true) (by decide)

/-- Insert a new pair `(0, j)` ahead of a smaller pairing. -/
noncomputable def Pairing.insertFirstPair {n : ℕ} (pairing : Pairing n) (j : Fin (2 * (n + 1)))
    (hj : j ≠ (0 : Fin (2 * (n + 1)))) : Pairing (n + 1) :=
  (boolPairing.sumCongr pairing).transport (deletedPositionsSumEquiv (2 * n) j hj).symm

@[simp]
theorem Pairing.insertFirstPair_partner_zero {n : ℕ} (pairing : Pairing n)
    (j : Fin (2 * (n + 1))) (hj : j ≠ (0 : Fin (2 * (n + 1)))) :
    (pairing.insertFirstPair j hj).partner 0 = j := by
  let e := deletedPositionsSumEquiv (2 * n) j hj
  change ((boolPairing.sumCongr pairing).transport e.symm).partner
    (e (Sum.inl false)) = e (Sum.inl true)
  rw [PairingOn.transport_partner, Equiv.symm_apply_apply, PairingOn.sumCongr_partner_inl]
  rfl

private theorem Pairing.insertFirstPair_partner_orderIso {n : ℕ} (pairing : Pairing n)
    (j : Fin (2 * (n + 1))) (hj : j ≠ (0 : Fin (2 * (n + 1)))) (i : Fin (2 * n)) :
    (pairing.insertFirstPair j hj).partner
        (deletedPositionsOrderIso (2 * n) j hj i : Fin (2 * (n + 1))) =
      (deletedPositionsOrderIso (2 * n) j hj (pairing.partner i) : Fin (2 * (n + 1))) := by
  let e := deletedPositionsSumEquiv (2 * n) j hj
  change ((boolPairing.sumCongr pairing).transport e.symm).partner
    (e (Sum.inr i)) = e (Sum.inr (pairing.partner i))
  rw [PairingOn.transport_partner, Equiv.symm_apply_apply, PairingOn.sumCongr_partner_inr]
  rfl

/-- Inserting and then erasing the new first pair recovers the smaller pairing. -/
theorem Pairing.eraseZeroPair_insertFirstPair {n : ℕ} (pairing : Pairing n)
    (j : Fin (2 * (n + 1))) (hj : j ≠ (0 : Fin (2 * (n + 1)))) :
    (pairing.insertFirstPair j hj).eraseZeroPair = pairing := by
  let P := pairing.insertFirstPair j hj
  apply PairingOn.ext
  apply Equiv.ext
  intro i
  apply P.eraseZeroOrderIso.injective
  apply Subtype.ext
  calc
    (P.eraseZeroOrderIso (P.eraseZeroPair.partner i) : Fin (2 * (n + 1))) =
        P.partner (P.eraseZeroOrderIso i) := P.eraseZeroOrderIso_partner i
    _ = P.eraseZeroOrderIso (pairing.partner i) :=
      pairing.insertFirstPair_partner_orderIso j hj i

/-- Erasing and reinserting the first pair recovers the original pairing. -/
theorem Pairing.insertFirstPair_eraseZeroPair {n : ℕ} (pairing : Pairing (n + 1)) :
    pairing.eraseZeroPair.insertFirstPair (pairing.partner 0)
      (pairing.partner_ne 0) = pairing := by
  let P := pairing.eraseZeroPair.insertFirstPair (pairing.partner 0) (pairing.partner_ne 0)
  let e := deletedPositionsSumEquiv (2 * n) (pairing.partner 0) (pairing.partner_ne 0)
  apply PairingOn.ext
  apply Equiv.ext
  intro x
  obtain ⟨y, rfl⟩ := e.surjective x
  rcases y with b | i
  · cases b
    · exact pairing.eraseZeroPair.insertFirstPair_partner_zero (pairing.partner 0)
        (pairing.partner_ne 0)
    · change P.partner (pairing.partner 0) = pairing.partner (pairing.partner 0)
      have h := P.partner_partner 0
      have hzero : P.partner 0 = pairing.partner 0 :=
        pairing.eraseZeroPair.insertFirstPair_partner_zero (pairing.partner 0)
          (pairing.partner_ne 0)
      rw [hzero] at h
      exact h.trans (pairing.partner_partner 0).symm
  · exact (pairing.eraseZeroPair.insertFirstPair_partner_orderIso (pairing.partner 0)
      (pairing.partner_ne 0) i).trans (pairing.eraseZeroOrderIso_partner i)

/-- A pairing decomposes into the partner of `0` and the smaller pairing obtained by erasing it. -/
noncomputable def Pairing.equivSigma (n : ℕ) :
    Pairing (n + 1) ≃ Σ _ : {j : Fin (2 * (n + 1)) // j ≠ (0 : Fin (2 * (n + 1)))}, Pairing n where
  toFun pairing := ⟨⟨pairing.partner 0, pairing.partner_ne 0⟩, pairing.eraseZeroPair⟩
  invFun jQ := jQ.2.insertFirstPair jQ.1.1 jQ.1.2
  left_inv pairing := pairing.insertFirstPair_eraseZeroPair
  right_inv jQ := by
    obtain ⟨⟨j, hj⟩, Q⟩ := jQ
    refine Sigma.ext (Subtype.ext ?_) ?_
    · exact Q.insertFirstPair_partner_zero j hj
    · exact heq_of_eq (Q.eraseZeroPair_insertFirstPair j hj)


/-- A product over `pairing.pairs` splits into the `firstPair` factor times a product over the
smaller pairing's own pairs. -/
theorem Pairing.prod_pairs_eq_firstPair_mul {n : ℕ} {M : Type*} [CommMonoid M]
    (pairing : Pairing (n + 1)) (f : Fin (2 * (n + 1)) × Fin (2 * (n + 1)) → M) :
    ∏ pr ∈ pairing.pairs, f pr =
      f pairing.firstPair *
        ∏ pr ∈ pairing.eraseZeroPair.pairs,
          f ((pairing.eraseZeroOrderIso pr.1 : Fin (2 * (n + 1))),
            (pairing.eraseZeroOrderIso pr.2 : Fin (2 * (n + 1)))) := by
  classical
  rw [← Finset.insert_erase pairing.firstPair_mem_pairs,
    pairing.pairs_erase_firstPair_eq_image]
  rw [Finset.prod_insert, Finset.prod_image]
  · rfl
  · intro p _ q _ h
    exact pairing.eraseZeroPairEmbedding.injective h
  · rw [← pairing.pairs_erase_firstPair_eq_image]
    simp

/-- A sum over `Pairing (n + 1)`, reindexed as a double sum over a peeled position and the smaller
pairing. -/
theorem Pairing.sum_eq_sum_sum_insertFirstPair {n : ℕ} {M : Type*} [AddCommMonoid M]
    (F : Pairing (n + 1) → M) :
    ∑ pairing : Pairing (n + 1), F pairing =
      ∑ j : Fin (2 * n + 1), ∑ Q : Pairing n,
        F (Q.insertFirstPair j.succ (Fin.succ_ne_zero j)) := by
  rw [← Equiv.sum_comp (Pairing.equivSigma n).symm F, Fintype.sum_sigma]
  let e :
      {j : Fin (2 * (n + 1)) // j ≠ 0} ≃ Fin (2 * n + 1) :=
    (finSuccAboveEquiv (0 : Fin (2 * n + 2))).symm
  refine Fintype.sum_equiv e
    (fun x => ∑ Q : Pairing n, F ((Pairing.equivSigma n).symm ⟨x, Q⟩))
    (fun j => ∑ Q : Pairing n, F (Q.insertFirstPair j.succ (Fin.succ_ne_zero j)))
    fun x => ?_
  apply Finset.sum_congr rfl
  intro Q _
  have hxSubtype :=
    (finSuccAboveEquiv (0 : Fin (2 * n + 2))).apply_symm_apply x
  have hx : (e x).succ = x.1 := by
    change ((finSuccAboveEquiv (0 : Fin (2 * n + 2))).symm x).succ = x.1
    have hxVal := congrArg Subtype.val hxSubtype
    rw [finSuccAboveEquiv_apply] at hxVal
    simpa using hxVal
  simp only [Pairing.equivSigma, Equiv.coe_fn_symm_mk, hx]

end Combinatorics
