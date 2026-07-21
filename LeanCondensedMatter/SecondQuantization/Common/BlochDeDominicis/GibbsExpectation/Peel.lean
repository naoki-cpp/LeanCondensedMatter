import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.GibbsExpectation.Core
import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.PeelFirstTrace
import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.PeelTermsIndexed

set_option linter.style.header false

/-!
# The normalized peel identity, and its indexed `Finset.sum` form

Divides `BlochDeDominicis/PeelFirstTrace.lean`'s un-normalized peel identity through by the
genuine partition function, then rewrites the result as an indexed `Finset.sum` over positions —
the form the general `n`-point induction (`Common/BlochDeDominicis/Induction.lean`) actually
recurses on.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*} [Fintype Config]

/-- **The normalized peel-first identity**, dividing `PeelFirstTrace.lean`'s un-normalized
`(1 - ζ^{l.length}w₁) Tr[e^{-βH₀}(C₁·B₁⋯Bₖ)] = Tr[e^{-βH₀}·peelSum ζ l]` through by the genuine
partition function: `⟨C₁B₁⋯Bₖ⟩ = ⟨peelSum ζ l⟩ / (1 - ζ^{l.length}w₁)`. The general list-indexed
counterpart of `TwoPoint.lean`'s `gibbsExpectation_comp_eq_div_of_zetaCommutator`. -/
theorem gibbsExpectation_peel (energy : Config → ℝ) (β q1 : ℝ) (ζ : ℂ)
    (C1 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (l : List ((AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) × ℂ))
    (hC1 : heisenbergEvolve energy (-β) C1 = Complex.exp ((q1 * (-β) : ℝ) : ℂ) • C1)
    (hcomm : ∀ p ∈ l, zetaCommutator ζ C1 p.1 =
      p.2 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hZ : traceFock (diagonalEvolution energy (-β)) ≠ 0)
    (hne : (1 : ℂ) - ζ ^ l.length * Complex.exp ((q1 * β : ℝ) : ℂ) ≠ 0) :
    gibbsExpectation energy β (C1.comp (prodComp (l.map Prod.fst))) =
      gibbsExpectation energy β (peelSum ζ l) / (1 - ζ ^ l.length * Complex.exp ((q1 * β : ℝ) : ℂ))
    := by
  have h := traceFock_diagonalEvolution_comp_peel energy β q1 ζ C1 l hC1 hcomm
  have hne' : (1 : ℂ) - ζ ^ l.length * Complex.exp ((β * q1 : ℝ) : ℂ) ≠ 0 := by
    rwa [mul_comm β q1]
  simp only [gibbsExpectation_eq_normalizedWeightedDiagonal, normalizedWeightedDiagonal,
    ← traceFock_diagonalEvolution_comp_eq_weightedTrace, ← traceFock_diagonalEvolution_eq_weightSum]
  field_simp [hne']
  linear_combination (norm := ring_nf) h

/-- **`gibbsExpectation` of `peelSum`, as an indexed `Finset.sum`**: dividing `peelSum`'s
recursive/`List.sum` structure into its `peelTerms_eq_ofFn`-closed-form individual terms and
applying `gibbsExpectation`'s linearity to each, `⟨peelSum ζ l⟩ = Σⱼ ζʲcⱼ⟨remaining product with
the `j`-th operator erased⟩` — the physics reference notes' `Σⱼ ζʲc₁ⱼ⟨…Ĉⱼ…⟩` presentation, now at
the level of normalized numbers rather than un-normalized traces or a bare `List.sum`. -/
theorem gibbsExpectation_peelSum_eq_sum (energy : Config → ℝ) (β : ℝ) (ζ : ℂ)
    (l : List ((AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) × ℂ)) :
    gibbsExpectation energy β (peelSum ζ l) =
      ∑ j : Fin l.length, ζ ^ (j : ℕ) * (l[(j : ℕ)]'j.isLt).2 *
        gibbsExpectation energy β (prodComp ((l.eraseIdx j).map Prod.fst)) := by
  rw [peelSum_eq_peelTerms_sum, peelTerms_eq_ofFn, gibbsExpectation_list_sum, List.map_ofFn,
    List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Function.comp, gibbsExpectation_smul, mul_assoc]

/-- **The normalized peel identity, as an indexed `Finset.sum`**: combines `gibbsExpectation_peel`
with `gibbsExpectation_peelSum_eq_sum` to give `⟨C₁B₁⋯Bₖ⟩` directly as a sum of normalized terms
over positions, rather than `⟨peelSum ζ l⟩` left opaque — the piece the general `n`-point induction
(`notes/roadmaps/second-quantization.md`'s Phase 9) actually recurses on. -/
theorem gibbsExpectation_peel_indexed (energy : Config → ℝ) (β q1 : ℝ) (ζ : ℂ)
    (C1 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (l : List ((AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) × ℂ))
    (hC1 : heisenbergEvolve energy (-β) C1 = Complex.exp ((q1 * (-β) : ℝ) : ℂ) • C1)
    (hcomm : ∀ p ∈ l, zetaCommutator ζ C1 p.1 =
      p.2 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hZ : traceFock (diagonalEvolution energy (-β)) ≠ 0)
    (hne : (1 : ℂ) - ζ ^ l.length * Complex.exp ((q1 * β : ℝ) : ℂ) ≠ 0) :
    gibbsExpectation energy β (C1.comp (prodComp (l.map Prod.fst))) =
      (∑ j : Fin l.length, ζ ^ (j : ℕ) * (l[(j : ℕ)]'j.isLt).2 *
          gibbsExpectation energy β (prodComp ((l.eraseIdx j).map Prod.fst))) /
        (1 - ζ ^ l.length * Complex.exp ((q1 * β : ℝ) : ℂ)) := by
  rw [gibbsExpectation_peel energy β q1 ζ C1 l hC1 hcomm hZ hne, gibbsExpectation_peelSum_eq_sum]

end Common
end SecondQuantization
