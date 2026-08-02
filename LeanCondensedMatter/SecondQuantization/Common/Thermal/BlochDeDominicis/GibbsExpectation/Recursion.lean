import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.ExpectationRecursion
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.GibbsExpectation.TwoPoint
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.GibbsExpectation.Peel

set_option linter.style.header false

/-!
# Finite Gibbs implementation of the expectation pairing recursion

This module discharges the abstract `ExpectationPairingRecursion` contract for the canonical finite
Gibbs density-state expectation.  All finite-configuration, diagonal-evolution, and trace-ratio
facts are confined to this implementation; the arbitrary-length pairing induction itself is
independent of them.
-/

namespace SecondQuantization
namespace Common
namespace BlochDeDominicis

variable {Config : Type*} [Fintype Config] [Nonempty Config]

/-- The finite Gibbs expectation, together with its KMS first-pair recurrence, as an implementation
of the generic Bloch–de Dominicis recursion contract. -/
noncomputable def finiteGibbsExpectationRecursion (s : Statistics)
    (energy : Config → ℝ) (β : ℝ)
    (hZ : traceFock (diagonalEvolution energy (-β)) ≠ 0) :
    ExpectationPairingRecursion
      (AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) s where
  expectation := fun l => finiteGibbsExpectation energy β (prodComp l)
  pairValue := fun A B => finiteGibbsExpectation energy β (A.comp B)
  admissible := fun n C => ∃ (q : Fin (2 * n) → ℝ) (c : Fin (2 * n) → Fin (2 * n) → ℂ),
    (∀ i, heisenbergEvolve energy (-β) (C i) =
      Complex.exp ((q i * (-β) : ℝ) : ℂ) • C i) ∧
    (∀ i j, i ≠ j → zetaCommutator (s.zetaInt : ℂ) (C i) (C j) =
      c i j • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)) ∧
    (∀ i, (1 : ℂ) - (s.zetaInt : ℂ) * Complex.exp ((q i * β : ℝ) : ℂ) ≠ 0)
  expectation_nil := by
    simp only [prodComp_nil]
    exact finiteGibbsExpectation_id energy β
  admissible_erase := by
    rintro n C ⟨q, c, hC, hcomm, hne⟩ j
    exact ⟨fun i => q ((j.succAbove i).succ), fun i i' => c ((j.succAbove i).succ)
      ((j.succAbove i').succ), fun i => hC _, fun i i' h => hcomm _ _
        (fun heq => h (Fin.succAbove_right_injective (Fin.succ_injective _ heq))),
      fun i => hne _⟩
  expectation_succ := by
    rintro m C ⟨q, c, hC, hcomm, hne⟩
    have h1 : finiteGibbsExpectation energy β (prodComp (List.ofFn C)) =
        finiteGibbsExpectation energy β
          ((C 0).comp (prodComp (List.ofFn (fun i : Fin (2 * m + 1) => C i.succ)))) := by
      rw [List.ofFn_succ, prodComp_cons]
      rfl
    set l : List ((AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) × ℂ) :=
      List.ofFn (fun i : Fin (2 * m + 1) => (C i.succ, c 0 i.succ)) with hl
    have hlmap : l.map Prod.fst = List.ofFn (fun i : Fin (2 * m + 1) => C i.succ) := by
      rw [hl, List.map_ofFn]
      rfl
    have hlen : l.length = 2 * m + 1 := by
      rw [hl]
      simp
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
    have hne0 : (1 : ℂ) - (s.zetaInt : ℂ) ^ l.length *
        Complex.exp ((q 0 * β : ℝ) : ℂ) ≠ 0 := by
      rw [hzl]
      exact hne 0
    have hpeel := finiteGibbsExpectation_peel_indexed energy β (q 0) (s.zetaInt : ℂ) (C 0) l
      (hC 0) hcommL hZ hne0
    rw [hlmap] at hpeel
    let hcast : Fin l.length ≃ Fin (2 * m + 1) :=
      ⟨Fin.cast hlen, Fin.cast hlen.symm, fun i => rfl, fun i => rfl⟩
    have hreindex :
        (∑ i : Fin l.length, (s.zetaInt : ℂ) ^ (i : ℕ) * l[(i : ℕ)].2 *
            finiteGibbsExpectation energy β (prodComp ((l.eraseIdx (i : ℕ)).map Prod.fst))) =
          ∑ j : Fin (2 * m + 1), (s.zetaInt : ℂ) ^ (j : ℕ) *
            (l[(j : ℕ)]'(by rw [hlen]; exact j.isLt)).2 *
              finiteGibbsExpectation energy β
                (prodComp ((l.eraseIdx (j : ℕ)).map Prod.fst)) :=
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
    have h2 : finiteGibbsExpectation energy β ((C 0).comp (C j.succ)) =
        c 0 j.succ / (1 - (s.zetaInt : ℂ) * Complex.exp ((q 0 * β : ℝ) : ℂ)) :=
      finiteGibbsExpectation_comp_eq_div_of_zetaCommutator energy β (q 0) (s.zetaInt : ℂ)
        (c 0 j.succ) (C 0) (C j.succ) (hC 0)
        (hcomm 0 j.succ (Ne.symm (Fin.succ_ne_zero j))) hZ (hne 0)
    rw [hljfst, hljsnd, h2]
    ring

end BlochDeDominicis
end Common
end SecondQuantization
