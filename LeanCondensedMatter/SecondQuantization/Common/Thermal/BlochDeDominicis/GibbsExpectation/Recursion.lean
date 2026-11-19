import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.ExpectationRecursion
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.GibbsExpectation.TwoPoint
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized.PeelFirstTrace

set_option linter.style.header false

/-!
# Finite Gibbs peeling and expectation pairing recursion

This module records the normalized four-point specialization and discharges the abstract
`ExpectationPairingRecursion` contract for the canonical finite Gibbs density-state expectation.  All finite-configuration, diagonal-evolution, and trace-ratio
facts are confined to this implementation; the arbitrary-length pairing induction itself is
independent of them.
-/

namespace SecondQuantization
namespace Common

/-!
## Finite Gibbs indexed peel and four-point specialization

The normalized peel identity specializes the finite Gibbs trace relation to an indexed sum.
The four-point formula then follows from the indexed peel and normalized two-point identities.
It allows a general complex exchange factor `ζ` satisfying `ζ² = 1`, independently of the
statistics-indexed arbitrary-length recursion below.
-/

section

variable {Config : Type*} [Fintype Config] [Nonempty Config]

/-- The normalized peel identity, as an indexed `Finset.sum`. -/
theorem finiteGibbsExpectation_peel_indexed (energy : Config → ℝ) (β q1 : ℝ) (ζ : ℂ)
    (C1 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (l : List ((AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) × ℂ))
    (hC1 : heisenbergEvolve energy (-β) C1 = Complex.exp ((q1 * (-β) : ℝ) : ℂ) • C1)
    (hcomm : ∀ p ∈ l, ScalarExchange.zetaCommutator ζ C1 p.1 =
      p.2 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hne : (1 : ℂ) - ζ ^ l.length * Complex.exp ((q1 * β : ℝ) : ℂ) ≠ 0) :
    finiteGibbsExpectation energy β (C1.comp (List.prod (l.map Prod.fst))) =
      (∑ j : Fin l.length, ζ ^ (j : ℕ) * (l[(j : ℕ)]'j.isLt).2 *
          finiteGibbsExpectation energy β (List.prod ((l.eraseIdx j).map Prod.fst))) /
        (1 - ζ ^ l.length * Complex.exp ((q1 * β : ℝ) : ℂ)) := by
  have hpeel :
      finiteGibbsExpectation energy β (C1.comp (List.prod (l.map Prod.fst))) =
        finiteGibbsExpectation energy β (ScalarExchange.peelSumWithCoefficients ζ l) /
          (1 - ζ ^ l.length * Complex.exp ((q1 * β : ℝ) : ℂ)) := by
    have h := tsumTrace_diagonalEvolution_comp_peel energy β q1 ζ C1 l hC1 hcomm
      Summable.of_finite Summable.of_finite
    simp only [tsumTrace, tsum_fintype, ← traceFock_eq_sum_matrixCoeff] at h
    have hZ := traceFock_diagonalEvolution_ne_zero energy β
    have hne' : (1 : ℂ) - ζ ^ l.length * Complex.exp ((β * q1 : ℝ) : ℂ) ≠ 0 := by
      rwa [mul_comm β q1]
    simp only [finiteGibbsExpectation_eq_trace_div]
    field_simp [hZ, hne']
    linear_combination (norm := ring_nf) h
  rw [hpeel]
  apply congrArg (fun x : ℂ =>
    x / (1 - ζ ^ l.length * Complex.exp ((q1 * β : ℝ) : ℂ)))
  change (finiteGibbsExpectationLinearMap energy β)
    (ScalarExchange.peelSumWithCoefficients ζ l) = _
  rw [ScalarExchange.peelSumWithCoefficients_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [finiteGibbsExpectation, smul_smul, smul_eq_mul, mul_assoc] using
    (finiteGibbsExpectationLinearMap energy β).map_smul
      (ζ ^ (j : ℕ) * (l[(j : ℕ)]'j.isLt).2)
      (List.prod ((l.eraseIdx j).map Prod.fst))

/-- The genuine normalized 4-point Bloch–de Dominicis expansion. -/
theorem finiteGibbsExpectation_four_point (energy : Config → ℝ) (β q1 : ℝ)
    (ζ c12 c13 c14 : ℂ)
    (C1 C2 C3 C4 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hC1 : heisenbergEvolve energy (-β) C1 = Complex.exp ((q1 * (-β) : ℝ) : ℂ) • C1)
    (hcomm12 : C1.comp C2 - ζ • (C2.comp C1) =
      c12 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hcomm13 : C1.comp C3 - ζ • (C3.comp C1) =
      c13 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hcomm14 : C1.comp C4 - ζ • (C4.comp C1) =
      c14 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hζ2 : ζ ^ 2 = 1)
    (hne : (1 : ℂ) - ζ * Complex.exp ((q1 * β : ℝ) : ℂ) ≠ 0) :
    finiteGibbsExpectation energy β (C1.comp (C2.comp (C3.comp C4))) =
      finiteGibbsExpectation energy β (C1.comp C2) *
          finiteGibbsExpectation energy β (C3.comp C4) +
        ζ * finiteGibbsExpectation energy β (C1.comp C3) *
          finiteGibbsExpectation energy β (C2.comp C4) +
        finiteGibbsExpectation energy β (C1.comp C4) *
          finiteGibbsExpectation energy β (C2.comp C3) := by
  have hζ3 : ζ ^ 3 = ζ := by
    have h32 : ζ ^ 3 = ζ ^ 2 * ζ := by ring
    rw [h32, hζ2, one_mul]
  have h4 :
    finiteGibbsExpectation energy β (C1.comp (C2.comp (C3.comp C4))) =
      (c12 * finiteGibbsExpectation energy β (C3.comp C4) +
          ζ * c13 * finiteGibbsExpectation energy β (C2.comp C4) +
          ζ ^ 2 * c14 * finiteGibbsExpectation energy β (C2.comp C3)) /
        (1 - ζ ^ 3 * Complex.exp ((q1 * β : ℝ) : ℂ)) := by
    have hmem : ∀ p ∈ [(C2, c12), (C3, c13), (C4, c14)],
        ScalarExchange.zetaCommutator ζ C1 p.1 =
          p.2 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) := by
      intro p hp
      fin_cases hp
      · simpa [ScalarExchange.zetaCommutator, Module.End.mul_eq_comp] using hcomm12
      · simpa [ScalarExchange.zetaCommutator, Module.End.mul_eq_comp] using hcomm13
      · simpa [ScalarExchange.zetaCommutator, Module.End.mul_eq_comp] using hcomm14
    have hpeel := finiteGibbsExpectation_peel_indexed energy β q1 ζ C1
      [(C2, c12), (C3, c13), (C4, c14)] hC1 hmem
      (by simpa [hζ3] using hne)
    simpa [Fin.sum_univ_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Module.End.mul_eq_comp, Module.End.one_eq_id, add_assoc] using hpeel
  rw [hζ3, hζ2] at h4
  have h12 := finiteGibbsExpectation_comp_eq_div_of_zetaCommutator energy β q1 ζ c12 C1 C2 hC1
    hcomm12 hne
  have h13 := finiteGibbsExpectation_comp_eq_div_of_zetaCommutator energy β q1 ζ c13 C1 C3 hC1
    hcomm13 hne
  have h14 := finiteGibbsExpectation_comp_eq_div_of_zetaCommutator energy β q1 ζ c14 C1 C4 hC1
    hcomm14 hne
  rw [h4, h12, h13, h14]
  field_simp

end

namespace BlochDeDominicis

variable {Config : Type*} [Fintype Config] [Nonempty Config]

/-- The finite Gibbs expectation, together with its KMS first-pair recurrence, as an implementation
of the generic Bloch–de Dominicis recursion contract. -/
noncomputable def finiteGibbsExpectationRecursion (s : Statistics)
    (energy : Config → ℝ) (β : ℝ) :
    ExpectationPairingRecursion
      (AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) s where
  expectation := fun l => finiteGibbsExpectation energy β l.prod
  pairValue := fun A B => finiteGibbsExpectation energy β (A.comp B)
  admissible := fun n C => ∃ (q : Fin (2 * n) → ℝ) (c : Fin (2 * n) → Fin (2 * n) → ℂ),
    (∀ i, heisenbergEvolve energy (-β) (C i) =
      Complex.exp ((q i * (-β) : ℝ) : ℂ) • C i) ∧
    (∀ i j, i ≠ j → ScalarExchange.zetaCommutator (s.zetaInt : ℂ) (C i) (C j) =
      c i j • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)) ∧
    (∀ i, (1 : ℂ) - (s.zetaInt : ℂ) * Complex.exp ((q i * β : ℝ) : ℂ) ≠ 0)
  expectation_nil := by
    simpa [Module.End.one_eq_id] using finiteGibbsExpectation_id energy β
  admissible_erase := by
    rintro n C ⟨q, c, hC, hcomm, hne⟩ j
    exact ⟨fun i => q ((j.succAbove i).succ), fun i i' => c ((j.succAbove i).succ)
      ((j.succAbove i').succ), fun i => hC _, fun i i' h => hcomm _ _
        (fun heq => h (Fin.succAbove_right_injective (Fin.succ_injective _ heq))),
      fun i => hne _⟩
  expectation_succ := by
    rintro m C ⟨q, c, hC, hcomm, hne⟩
    rw [List.ofFn_succ, List.prod_cons, Module.End.mul_eq_comp]
    set l : List ((AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) × ℂ) :=
      List.ofFn (fun i : Fin (2 * m + 1) => (C i.succ, c 0 i.succ)) with hl
    have hlmap : l.map Prod.fst = List.ofFn (fun i : Fin (2 * m + 1) => C i.succ) := by
      rw [hl, List.map_ofFn]
      rfl
    have hcommL : ∀ p ∈ l, ScalarExchange.zetaCommutator (s.zetaInt : ℂ) (C 0) p.1 =
        p.2 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) := by
      intro p hp
      rw [hl, List.mem_ofFn] at hp
      obtain ⟨i, rfl⟩ := hp
      exact hcomm 0 i.succ (Ne.symm (Fin.succ_ne_zero i))
    have hzl : (s.zetaInt : ℂ) ^ l.length = (s.zetaInt : ℂ) := by
      simpa [hl] using
        (zetaInt_pow_eq_of_mod_two_eq s (a := 2 * m + 1) (b := 1) (by omega))
    have hne0 : (1 : ℂ) - (s.zetaInt : ℂ) ^ l.length *
        Complex.exp ((q 0 * β : ℝ) : ℂ) ≠ 0 := by
      rw [hzl]
      exact hne 0
    have hpeel := finiteGibbsExpectation_peel_indexed energy β (q 0) (s.zetaInt : ℂ) (C 0) l
      (hC 0) hcommL hne0
    rw [hlmap] at hpeel
    rw [hzl] at hpeel
    rw [hl, List.sum_getElem_eraseIdx_ofFn
      (fun i : Fin (2 * m + 1) => (C i.succ, c 0 i.succ))
      (fun i p rest => (s.zetaInt : ℂ) ^ i * p.2 *
        finiteGibbsExpectation energy β (List.prod (rest.map Prod.fst)))] at hpeel
    change finiteGibbsExpectation energy β
        ((C 0).comp (List.prod (List.ofFn (fun i : Fin (2 * m + 1) => C i.succ)))) = _
    rw [hpeel, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h2 : finiteGibbsExpectation energy β ((C 0).comp (C j.succ)) =
        c 0 j.succ / (1 - (s.zetaInt : ℂ) * Complex.exp ((q 0 * β : ℝ) : ℂ)) :=
      finiteGibbsExpectation_comp_eq_div_of_zetaCommutator energy β (q 0) (s.zetaInt : ℂ)
        (c 0 j.succ) (C 0) (C j.succ) (hC 0)
        (hcomm 0 j.succ (Ne.symm (Fin.succ_ne_zero j))) (hne 0)
    simp only [List.map_ofFn, Function.comp_def]
    rw [h2]
    ring

open Combinatorics

/-- **Finite-configuration Gibbs specialization of the Bloch–de Dominicis pairing theorem.** The original linked-diagram
and finite-temperature pairing development is C. Bloch and C. de Dominicis, *Nuclear Physics*
**7**, 459–479 (1958),
[doi:10.1016/0029-5582(58)90285-2](https://doi.org/10.1016/0029-5582(58)90285-2).
For the unified bosonic/fermionic thermal Wick argument motivating this pairing formula, see M. Gaudin, *Nuclear
Physics* **15**, 89–91 (1960),
[doi:10.1016/0029-5582(60)90285-6](https://doi.org/10.1016/0029-5582(60)90285-6). This theorem is
the finite-Gibbs recursion specialization; it does not claim the infinite-volume
or interacting-state generality of the original diagrammatic development. -/
theorem finiteGibbsExpectation_prod_eq_sum_pairing (s : Statistics)
    (energy : Config → ℝ) (β : ℝ) :
    ∀ (n : ℕ) (C : Fin (2 * n) → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
      (q : Fin (2 * n) → ℝ) (c : Fin (2 * n) → Fin (2 * n) → ℂ),
      (∀ i, heisenbergEvolve energy (-β) (C i) = Complex.exp ((q i * (-β) : ℝ) : ℂ) • C i) →
      (∀ i j, i ≠ j → ScalarExchange.zetaCommutator (s.zetaInt : ℂ) (C i) (C j) =
        c i j • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)) →
      (∀ i, (1 : ℂ) - (s.zetaInt : ℂ) * Complex.exp ((q i * β : ℝ) : ℂ) ≠ 0) →
      finiteGibbsExpectation energy β (List.prod (List.ofFn C)) =
        ∑ pairing : Pairing n,
          pairing.weight s *
            ∏ pr ∈ pairing.pairs,
              finiteGibbsExpectation energy β ((C pr.1).comp (C pr.2)) := by
  intro n C q c hC hcomm hne
  exact (finiteGibbsExpectationRecursion s energy β).bloch_de_dominicis
    n C ⟨q, c, hC, hcomm, hne⟩


end BlochDeDominicis
end Common
end SecondQuantization
