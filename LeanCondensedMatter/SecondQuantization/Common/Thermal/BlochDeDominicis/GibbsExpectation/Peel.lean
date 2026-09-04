import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.GibbsExpectation.Core
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized.PeelFirstTrace
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized.PeelTermsIndexed

set_option linter.style.header false

/-!
# The normalized peel identity, and its indexed `Finset.sum` form

Divides `BlochDeDominicis/Unnormalized/PeelFirstTrace.lean`'s un-normalized peel identity through by
the genuine partition function, then rewrites the result as an indexed `Finset.sum` over positions —
the form the general `n`-point induction (`Common/Thermal/BlochDeDominicis/Induction.lean`) actually
recurses on.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*} [Fintype Config] [Nonempty Config]

/-- The normalized peel-first identity in the canonical finite Gibbs density state. -/
theorem finiteGibbsExpectation_peel (energy : Config → ℝ) (β q1 : ℝ) (ζ : ℂ)
    (C1 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (l : List ((AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) × ℂ))
    (hC1 : heisenbergEvolve energy (-β) C1 = Complex.exp ((q1 * (-β) : ℝ) : ℂ) • C1)
    (hcomm : ∀ p ∈ l, zetaCommutator ζ C1 p.1 =
      p.2 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hZ : traceFock (diagonalEvolution energy (-β)) ≠ 0)
    (hne : (1 : ℂ) - ζ ^ l.length * Complex.exp ((q1 * β : ℝ) : ℂ) ≠ 0) :
    finiteGibbsExpectation energy β (C1.comp (prodComp (l.map Prod.fst))) =
      finiteGibbsExpectation energy β (peelSum ζ l) /
        (1 - ζ ^ l.length * Complex.exp ((q1 * β : ℝ) : ℂ)) := by
  have h := traceFock_diagonalEvolution_comp_peel energy β q1 ζ C1 l hC1 hcomm
  have hne' : (1 : ℂ) - ζ ^ l.length * Complex.exp ((β * q1 : ℝ) : ℂ) ≠ 0 := by
    rwa [mul_comm β q1]
  simp only [finiteGibbsExpectation_eq_trace_div]
  field_simp [hZ, hne']
  linear_combination (norm := ring_nf) h

/-- The expectation of `peelSum`, written as an indexed finite sum. -/
theorem finiteGibbsExpectation_peelSum_eq_sum (energy : Config → ℝ) (β : ℝ) (ζ : ℂ)
    (l : List ((AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) × ℂ)) :
    finiteGibbsExpectation energy β (peelSum ζ l) =
      ∑ j : Fin l.length, ζ ^ (j : ℕ) * (l[(j : ℕ)]'j.isLt).2 *
        finiteGibbsExpectation energy β (prodComp ((l.eraseIdx j).map Prod.fst)) := by
  have hmap : ∀ L : List (AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config),
      finiteGibbsExpectation energy β L.sum =
        (L.map (finiteGibbsExpectation energy β)).sum := by
    intro L
    calc
      finiteGibbsExpectation energy β L.sum =
          finiteGibbsExpectationLinearMap energy β L.sum := rfl
      _ = (L.map ⇑(finiteGibbsExpectationLinearMap energy β)).sum :=
        map_list_sum (finiteGibbsExpectationLinearMap energy β) L
      _ = (L.map (finiteGibbsExpectation energy β)).sum := by
        apply congrArg List.sum
        exact List.map_congr_left fun _ _ => rfl
  rw [peelSum_eq_peelTerms_sum, peelTerms_eq_ofFn, hmap, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Function.comp]
  simpa only [finiteGibbsExpectation, smul_smul, smul_eq_mul, mul_assoc] using
    (finiteGibbsExpectationLinearMap energy β).map_smul
      (ζ ^ (j : ℕ) * (l[(j : ℕ)]'j.isLt).2)
      (prodComp ((l.eraseIdx j).map Prod.fst))

/-- The normalized peel identity, as an indexed `Finset.sum`. -/
theorem finiteGibbsExpectation_peel_indexed (energy : Config → ℝ) (β q1 : ℝ) (ζ : ℂ)
    (C1 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (l : List ((AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) × ℂ))
    (hC1 : heisenbergEvolve energy (-β) C1 = Complex.exp ((q1 * (-β) : ℝ) : ℂ) • C1)
    (hcomm : ∀ p ∈ l, zetaCommutator ζ C1 p.1 =
      p.2 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hZ : traceFock (diagonalEvolution energy (-β)) ≠ 0)
    (hne : (1 : ℂ) - ζ ^ l.length * Complex.exp ((q1 * β : ℝ) : ℂ) ≠ 0) :
    finiteGibbsExpectation energy β (C1.comp (prodComp (l.map Prod.fst))) =
      (∑ j : Fin l.length, ζ ^ (j : ℕ) * (l[(j : ℕ)]'j.isLt).2 *
          finiteGibbsExpectation energy β (prodComp ((l.eraseIdx j).map Prod.fst))) /
        (1 - ζ ^ l.length * Complex.exp ((q1 * β : ℝ) : ℂ)) := by
  rw [finiteGibbsExpectation_peel energy β q1 ζ C1 l hC1 hcomm hZ hne,
    finiteGibbsExpectation_peelSum_eq_sum]

end Common
end SecondQuantization
