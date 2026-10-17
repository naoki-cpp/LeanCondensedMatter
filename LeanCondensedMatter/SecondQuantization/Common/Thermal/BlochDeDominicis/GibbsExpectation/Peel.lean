import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsCoordinate
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized.PeelFirstTrace

set_option linter.style.header false

/-!
# Indexed finite Gibbs peeling identity

Specializes the summable trace peel identity to a finite Gibbs density-state expectation, then
expands the scalar-exchange peel sum by position. The indexed result is the input to the
general normalized `n`-point recursion.
-/

namespace SecondQuantization
namespace Common

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
  congr 1
  change (finiteGibbsExpectationLinearMap energy β)
    (ScalarExchange.peelSumWithCoefficients ζ l) = _
  rw [ScalarExchange.peelSumWithCoefficients_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [finiteGibbsExpectation, smul_smul, smul_eq_mul, mul_assoc] using
    (finiteGibbsExpectationLinearMap energy β).map_smul
      (ζ ^ (j : ℕ) * (l[(j : ℕ)]'j.isLt).2)
      (List.prod ((l.eraseIdx j).map Prod.fst))

end Common
end SecondQuantization
