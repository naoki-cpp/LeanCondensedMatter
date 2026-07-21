import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.GibbsExpectation.TwoPoint
import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.GibbsExpectation.Peel
import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.PairingWeight
import LeanCondensedMatter.Combinatorics.PerfectPairing.FirstPairRecursion

set_option linter.style.header false

/-!
# The general finite-temperature Bloch–de Dominicis theorem

The genuine `n`-point statement: a normalized Gibbs expectation of a `2n`-operator product is the
`Pairing n`-weighted sum of products of normalized 2-point values, generalizing
`GibbsExpectation/FourPoint.lean`'s `gibbsExpectation_four_point` (`n = 2`) to arbitrary `n`.

The combinatorial backbone — induction on `n`, the `equivSigma`/`insertFirstPair` double-sum
reindexing, and the `crossingCount`/`pairs` erase-zero recursions — is
`Combinatorics/PerfectPairing/FirstPairRecursion.lean`'s
`moment_eq_pairing_sum_of_first_pair_recursion`, stated with no `Statistics`/`ℂ`/`AlgebraicFock`
dependency. This file supplies only the analytic content that lemma's `Admissible`/`moment_succ`
hypotheses ask for: peeling the first operator off the front
(`gibbsExpectation_peel_indexed`), identifying the remaining `2(n-1)`-operator product's family
with the smaller pairing's positions directly via
`List.eraseIdx_ofFn_eq_ofFn_succAbove`/`Pairing.eraseZeroOrderIso_eq_succ_succAbove`, and
converting the peeled coefficient into a normalized 2-point value via
`gibbsExpectation_comp_eq_div_of_zetaCommutator`.
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
  have hζ : (s.zetaInt : ℂ) * (s.zetaInt : ℂ) = 1 := by
    have h := zetaInt_pow_eq_of_mod_two_eq s (a := 2) (b := 0) (by omega)
    simpa [pow_two] using h
  -- The `Admissible` predicate packages the eigenoperator, scalar-commutator, and non-resonance
  -- data `moment_succ`/`admissible_erase` need, existentially so it can be transported to erased
  -- subfamilies.
  set Admissible : (n : ℕ) →
      (Fin (2 * n) → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) → Prop :=
    fun n C => ∃ (q : Fin (2 * n) → ℝ) (c : Fin (2 * n) → Fin (2 * n) → ℂ),
      (∀ i, heisenbergEvolve energy (-β) (C i) = Complex.exp ((q i * (-β) : ℝ) : ℂ) • C i) ∧
      (∀ i j, i ≠ j → zetaCommutator (s.zetaInt : ℂ) (C i) (C j) =
        c i j • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)) ∧
      (∀ i, (1 : ℂ) - (s.zetaInt : ℂ) * Complex.exp ((q i * β : ℝ) : ℂ) ≠ 0) with hAdmDef
  have moment_zero : ∀ C : Fin 0 → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config,
      gibbsExpectation energy β (prodComp (List.ofFn C)) = 1 := by
    intro C
    have hZw : weightSum (boltzmannWeight energy β) ≠ 0 := by
      rw [← traceFock_diagonalEvolution_eq_weightSum]; exact hZ
    simp only [List.ofFn_zero, prodComp_nil]
    exact gibbsExpectation_id energy β hZw
  have admissible_erase : ∀ (n : ℕ)
      (C : Fin (2 * (n + 1)) → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config),
      Admissible (n + 1) C → ∀ j : Fin (2 * n + 1),
        Admissible n (fun i : Fin (2 * n) => C ((j.succAbove i).succ)) := by
    rintro m C ⟨q, c, hC, hcomm, hne⟩ j
    exact ⟨fun i => q ((j.succAbove i).succ), fun i i' => c ((j.succAbove i).succ)
      ((j.succAbove i').succ), fun i => hC _, fun i i' h => hcomm _ _
        (fun heq => h (Fin.succAbove_right_injective (Fin.succ_injective _ heq))),
      fun i => hne _⟩
  have moment_succ : ∀ (m : ℕ)
      (C : Fin (2 * (m + 1)) → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config),
      Admissible (m + 1) C →
      gibbsExpectation energy β (prodComp (List.ofFn C)) =
        ∑ j : Fin (2 * m + 1), (s.zetaInt : ℂ) ^ (j : ℕ) *
          gibbsExpectation energy β ((C 0).comp (C j.succ)) *
          gibbsExpectation energy β
            (prodComp (List.ofFn fun i : Fin (2 * m) => C ((j.succAbove i).succ))) := by
    rintro m C ⟨q, c, hC, hcomm, hne⟩
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
    rw [h1, hpeel, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hljfst : (l.eraseIdx (j : ℕ)).map Prod.fst =
        List.ofFn (fun i : Fin (2 * m) => C ((j.succAbove i).succ)) := by
      rw [hl, List.eraseIdx_ofFn_eq_ofFn_succAbove, List.map_ofFn]
      rfl
    have hljsnd : l[(j : ℕ)]'(by rw [hlen]; exact j.isLt) = (C j.succ, c 0 j.succ) := by
      simp only [hl, List.getElem_ofFn]
    have h2 : gibbsExpectation energy β (C 0 |>.comp (C j.succ)) =
        c 0 j.succ / (1 - (s.zetaInt : ℂ) * Complex.exp ((q 0 * β : ℝ) : ℂ)) :=
      gibbsExpectation_comp_eq_div_of_zetaCommutator energy β (q 0) (s.zetaInt : ℂ) (c 0 j.succ)
        (C 0) (C j.succ) (hC 0) (hcomm 0 j.succ (Ne.symm (Fin.succ_ne_zero j))) hZ (hne 0)
    rw [hljfst, hljsnd, h2]
    ring
  intro n C q c hC hcomm hne
  have hmoment := moment_eq_pairing_sum_of_first_pair_recursion (s.zetaInt : ℂ) hζ
    (fun n C => gibbsExpectation energy β (prodComp (List.ofFn C)))
    (fun A B => gibbsExpectation energy β (A.comp B)) Admissible moment_zero admissible_erase
    moment_succ n C ⟨q, c, hC, hcomm, hne⟩
  rw [hmoment]
  refine Finset.sum_congr rfl fun pairing _ => ?_
  rw [Pairing.weight]

end BlochDeDominicis
end Common
end SecondQuantization
