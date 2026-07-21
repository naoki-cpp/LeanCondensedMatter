import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.GibbsExpectation.TwoPoint
import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.GibbsExpectation.Peel
import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.PairingWeight
import LeanCondensedMatter.Combinatorics.PerfectPairing.EraseZeroSuccAbove
import LeanCondensedMatter.Combinatorics.PerfectPairing.PairsDecomposition
import LeanCondensedMatter.Combinatorics.PerfectPairing.SumDecomposition

set_option linter.style.header false

/-!
# The general finite-temperature Bloch–de Dominicis theorem

The genuine `n`-point statement: a normalized Gibbs expectation of a `2n`-operator product is the
`Pairing n`-weighted sum of products of normalized 2-point values, generalizing
`GibbsExpectation.lean`'s `gibbsExpectation_four_point` (`n = 2`) to arbitrary `n`. Proved by plain
induction on `n` (only the immediately-preceding case `m` is used, so ordinary `induction n`
suffices — not strong induction), following the physics reference notes' own proof strategy: peel
the first operator off the front (`gibbsExpectation_peel_indexed`), identify the remaining
`2(n-1)`-operator product's family with the smaller pairing's positions directly via
`List.eraseIdx_ofFn_eq_ofFn_succAbove`/`Pairing.eraseZeroOrderIso_eq_succ_succAbove` (the two
lemmas `Pairing.ofFn_comp_eraseZeroOrderIso_eq_eraseIdx` composes, used here individually rather
than through that composed form), apply the inductive hypothesis, and reassemble via
`Pairing.equivSigma` (`Pairing.sum_eq_sum_sum_insertFirstPair`), matching signs via
`Pairing.weight_eraseZeroPair` and the pairs decomposition via
`Pairing.prod_pairs_eq_firstPair_mul`.
-/

namespace SecondQuantization
namespace Common
namespace BlochDeDominicis

variable {Config : Type*} [Fintype Config]

/-- **The general finite-temperature Bloch–de Dominicis theorem.** -/
theorem gibbsExpectation_prodComp_eq_sum_pairing (s : Statistics) (energy : Config → ℝ) (β : ℝ)
    (hZ : traceFock (diagonalEvolution energy (-β)) ≠ 0) :
    ∀ (n : ℕ) (C : Fin (2 * n) → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
      (q : Fin (2 * n) → ℝ) (c : Fin (2 * n) → Fin (2 * n) → ℂ),
      (∀ i, heisenbergEvolve energy (-β) (C i) = Complex.exp ((q i * (-β) : ℝ) : ℂ) • C i) →
      (∀ i j, i ≠ j → zetaCommutator (s.zetaInt : ℂ) (C i) (C j) =
        c i j • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)) →
      (∀ i, (1 : ℂ) - (s.zetaInt : ℂ) * Complex.exp ((q i * β : ℝ) : ℂ) ≠ 0) →
      gibbsExpectation energy β (prodComp (List.ofFn C)) =
        ∑ pairing : Pairing n,
          pairing.weight s *
            ∏ pr ∈ pairing.pairs, gibbsExpectation energy β ((C pr.1).comp (C pr.2)) := by
  intro n
  induction n with
  | zero =>
    intro C q c _ _ _
    have p0 : Pairing 0 :=
      Pairing.ofPartner (Equiv.refl (Fin 0)) ⟨fun i => i.elim0, fun i => i.elim0⟩
    have hUniq : ∀ pairing : Pairing 0, pairing = p0 := fun pairing =>
      Pairing.ext (Equiv.ext fun i => i.elim0)
    have hZw : weightSum (boltzmannWeight energy β) ≠ 0 := by
      rw [← traceFock_diagonalEvolution_eq_weightSum]; exact hZ
    have hpairs0 : p0.pairs = (∅ : Finset (Fin 0 × Fin 0)) := by
      simp [Pairing.pairs]
    have hcc0 : p0.crossingCount = 0 := by simp [Pairing.crossingCount, hpairs0]
    simp only [List.ofFn_zero, prodComp_nil]
    rw [gibbsExpectation_id energy β hZw, Fintype.sum_eq_single p0
      (fun pairing hne => absurd (hUniq pairing) hne)]
    simp [Pairing.weight, hpairs0, hcc0]
  | succ m ih =>
    intro C q c hC hcomm hne
    have h1 : gibbsExpectation energy β (prodComp (List.ofFn C)) =
        gibbsExpectation energy β
          ((C 0).comp (prodComp (List.ofFn (fun i : Fin (2 * m + 1) => C i.succ)))) := by
      rw [List.ofFn_succ, prodComp_cons]
      rfl
    set l : List ((AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) × ℂ) :=
      List.ofFn (fun i : Fin (2 * m + 1) => (C i.succ, c 0 i.succ)) with hl
    have hlmap : l.map Prod.fst = List.ofFn (fun i : Fin (2 * m + 1) => C i.succ) := by
      rw [hl, List.map_ofFn]; rfl
    have hlen : l.length = 2 * m + 1 := by rw [hl]; simp
    have hcommL : ∀ p ∈ l, zetaCommutator (s.zetaInt : ℂ) (C 0) p.1 =
        p.2 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) := by
      intro p hp
      rw [hl, List.mem_ofFn] at hp
      obtain ⟨i, rfl⟩ := hp
      exact hcomm 0 i.succ (Ne.symm (Fin.succ_ne_zero i))
    have hzl : (s.zetaInt : ℂ) ^ l.length = (s.zetaInt : ℂ) := by
      rw [hlen]
      have h := zetaInt_pow_eq_of_mod_two_eq s (a := 2 * m + 1) (b := 1) (by omega)
      rwa [pow_one] at h
    have hne0 : (1 : ℂ) - (s.zetaInt : ℂ) ^ l.length * Complex.exp ((q 0 * β : ℝ) : ℂ) ≠ 0 := by
      rw [hzl]; exact hne 0
    have hpeel := gibbsExpectation_peel_indexed energy β (q 0) (s.zetaInt : ℂ) (C 0) l (hC 0)
      hcommL hZ hne0
    rw [hlmap] at hpeel
    let hcast : Fin l.length ≃ Fin (2 * m + 1) :=
      ⟨Fin.cast hlen, Fin.cast hlen.symm, fun i => rfl, fun i => rfl⟩
    have hreindex :
        (∑ i : Fin l.length, (s.zetaInt : ℂ) ^ (i : ℕ) * l[(i : ℕ)].2 *
            gibbsExpectation energy β (prodComp ((l.eraseIdx (i : ℕ)).map Prod.fst))) =
          ∑ j : Fin (2 * m + 1), (s.zetaInt : ℂ) ^ (j : ℕ) *
            (l[(j : ℕ)]'(by rw [hlen]; exact j.isLt)).2 *
              gibbsExpectation energy β (prodComp ((l.eraseIdx (j : ℕ)).map Prod.fst)) :=
      Fintype.sum_equiv hcast _ _ fun i => by
        have hv : ((hcast i : Fin (2 * m + 1)) : ℕ) = (i : ℕ) := by
          change ((Fin.cast hlen i : Fin (2 * m + 1)) : ℕ) = (i : ℕ)
          rfl
        simp only [hv]
    rw [hreindex] at hpeel
    rw [hzl] at hpeel
    rw [h1, hpeel]
    rw [Pairing.sum_eq_sum_sum_insertFirstPair
      (fun pairing : Pairing (m + 1) => pairing.weight s *
        ∏ pr ∈ pairing.pairs, gibbsExpectation energy β ((C pr.1).comp (C pr.2)))]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hljfst : (l.eraseIdx (j : ℕ)).map Prod.fst =
        List.ofFn (fun i : Fin (2 * m) => C ((j.succAbove i).succ)) := by
      rw [hl, List.eraseIdx_ofFn_eq_ofFn_succAbove, List.map_ofFn]
      rfl
    have hljsnd : l[(j : ℕ)]'(by rw [hlen]; exact j.isLt) = (C j.succ, c 0 j.succ) := by
      simp only [hl, List.getElem_ofFn]
    have hC' : ∀ i : Fin (2 * m),
        heisenbergEvolve energy (-β) (C ((j.succAbove i).succ)) =
          Complex.exp ((q ((j.succAbove i).succ) * (-β) : ℝ) : ℂ) • C ((j.succAbove i).succ) :=
      fun i => hC _
    have hcomm' : ∀ i i' : Fin (2 * m), i ≠ i' →
        zetaCommutator (s.zetaInt : ℂ) (C ((j.succAbove i).succ)) (C ((j.succAbove i').succ)) =
          c ((j.succAbove i).succ) ((j.succAbove i').succ) •
            (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :=
      fun i i' h => hcomm _ _
        (fun heq => h (Fin.succAbove_right_injective (Fin.succ_injective _ heq)))
    have hne' : ∀ i : Fin (2 * m),
        (1 : ℂ) - (s.zetaInt : ℂ) * Complex.exp ((q ((j.succAbove i).succ) * β : ℝ) : ℂ) ≠ 0 :=
      fun i => hne _
    have hIH := ih (fun i : Fin (2 * m) => C ((j.succAbove i).succ))
      (fun i : Fin (2 * m) => q ((j.succAbove i).succ))
      (fun i i' : Fin (2 * m) => c ((j.succAbove i).succ) ((j.succAbove i').succ))
      hC' hcomm' hne'
    have h2 : gibbsExpectation energy β (C 0 |>.comp (C j.succ)) =
        c 0 j.succ / (1 - (s.zetaInt : ℂ) * Complex.exp ((q 0 * β : ℝ) : ℂ)) :=
      gibbsExpectation_comp_eq_div_of_zetaCommutator energy β (q 0) (s.zetaInt : ℂ) (c 0 j.succ)
        (C 0) (C j.succ) (hC 0) (hcomm 0 j.succ (Ne.symm (Fin.succ_ne_zero j))) hZ (hne 0)
    rw [hljfst, hljsnd]
    change (s.zetaInt : ℂ) ^ (j : ℕ) * c 0 j.succ *
        gibbsExpectation energy β
          (prodComp (List.ofFn fun i : Fin (2 * m) => C (j.succAbove i).succ)) /
      (1 - (s.zetaInt : ℂ) * Complex.exp ((q 0 * β : ℝ) : ℂ)) =
        ∑ Q : Pairing m,
          (Q.insertFirstPair j.succ (Ne.symm (Fin.succ_ne_zero j))).weight s *
            ∏ pr ∈ (Q.insertFirstPair j.succ (Ne.symm (Fin.succ_ne_zero j))).pairs,
              gibbsExpectation energy β ((C pr.1).comp (C pr.2))
    rw [hIH, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro Q _
    set P := Q.insertFirstPair j.succ (Ne.symm (Fin.succ_ne_zero j)) with hP
    have hPe : P.eraseZeroPair = Q :=
      Q.eraseZeroPair_insertFirstPair j.succ (Ne.symm (Fin.succ_ne_zero j))
    have hP0 : P.partner 0 = j.succ :=
      Q.insertFirstPair_partner_zero j.succ (Ne.symm (Fin.succ_ne_zero j))
    have hweight : P.weight s = (s.zetaInt : ℂ) ^ (j : ℕ) * Q.weight s := by
      rw [Pairing.weight_eraseZeroPair, hPe]
      congr 2
      rw [Pairing.interveningPositionCount, hP0]
      simp
    have hpred : (P.partner 0).pred (P.partner_ne 0) = j := by
      apply Fin.succ_injective
      rw [Fin.succ_pred, hP0]
    have heraseiso : ∀ pr : Fin (2 * m), (P.eraseZeroOrderIso pr : Fin (2 * (m + 1))) =
        (j.succAbove pr).succ := by
      intro pr
      rw [P.eraseZeroOrderIso_eq_succ_succAbove, hpred]
    have hprod : ∏ pr ∈ P.pairs, gibbsExpectation energy β ((C pr.1).comp (C pr.2)) =
        gibbsExpectation energy β ((C 0).comp (C j.succ)) *
          ∏ pr ∈ Q.pairs, gibbsExpectation energy β
            ((C (j.succAbove pr.1).succ).comp (C (j.succAbove pr.2).succ)) := by
      rw [P.prod_pairs_eq_firstPair_mul]
      congr 1
      · rw [Pairing.firstPair, hP0]
      · rw [hPe]
        apply Finset.prod_congr rfl
        intro pr _
        rw [heraseiso pr.1, heraseiso pr.2]
    rw [hweight, hprod, h2]
    ring

end BlochDeDominicis
end Common
end SecondQuantization
