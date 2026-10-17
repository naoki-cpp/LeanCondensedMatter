import LeanCondensedMatter.Analysis.ScalarExchange.Basic
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsCoordinate
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.GibbsExpectation.TwoPointTrace
import LeanCondensedMatter.SecondQuantization.Common.Algebra.ExchangeCommutator

set_option linter.style.header false

/-!
# The genuine normalized 2-point Bloch–de Dominicis value

Specializes the normalized summable trace identity to finite configurations, where summability
is automatic, and identifies the trace ratio with the canonical finite Gibbs state expectation.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*} [Fintype Config] [Nonempty Config]

/-- **The genuine normalized 2-point Bloch–de Dominicis value**: `⟨C₁Cⱼ⟩ = c₁ⱼ/(1 - ζw₁)`,
dividing the singleton-tail peel identity `(1 - ζw₁) Tr[e^{-βH₀}(C₁Cⱼ)] = c₁ⱼ Tr[e^{-βH₀}]` through
by the genuine (nonzero) partition function and by the (assumed nonzero) `1 - ζw₁` factor —
matching the physics reference notes' `⟨Ĉ₁Ĉⱼ⟩ = C_{1,j}/(1 - ζw₁)` letter-for-letter rather than
leaving it as an un-divided trace equation. -/
theorem finiteGibbsExpectation_comp_eq_div_of_zetaCommutator (energy : Config → ℝ) (β q1 : ℝ)
    (ζ c1j : ℂ) (C1 Cj : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hC1 : heisenbergEvolve energy (-β) C1 = Complex.exp ((q1 * (-β) : ℝ) : ℂ) • C1)
    (hcomm : ScalarExchange.zetaCommutator ζ C1 Cj =
      c1j • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hne : (1 : ℂ) - ζ * Complex.exp ((q1 * β : ℝ) : ℂ) ≠ 0) :
    finiteGibbsExpectation energy β (C1.comp Cj) =
      c1j / (1 - ζ * Complex.exp ((q1 * β : ℝ) : ℂ)) := by
  classical
  rw [finiteGibbsExpectation_eq_trace_div]
  have hZ : tsumTrace (diagonalEvolution energy (-β)) ≠ 0 := by
    simpa only [tsumTrace, tsum_fintype, traceFock_eq_sum_matrixCoeff] using
      traceFock_diagonalEvolution_ne_zero energy β
  simpa only [tsumTrace, tsum_fintype, traceFock_eq_sum_matrixCoeff] using
    normalizedTsumTrace_comp_eq_div_of_zetaCommutator energy β q1 ζ c1j C1 Cj
      hC1 hcomm Summable.of_finite Summable.of_finite hZ hne

/-- **The `Statistics`-indexed presentation**, in terms of `exchangeCommutator s` rather than a
raw `ζ : ℂ` bracket — the form callers already holding a `Statistics` value should reach for. -/
theorem finiteGibbsExpectation_comp_eq_div_of_exchangeCommutator (energy : Config → ℝ) (β q1 : ℝ)
    (s : Statistics) (c1j : ℂ) (C1 Cj : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hC1 : heisenbergEvolve energy (-β) C1 = Complex.exp ((q1 * (-β) : ℝ) : ℂ) • C1)
    (hcomm : exchangeCommutator s C1 Cj =
      c1j • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hne : (1 : ℂ) - (s.zetaInt : ℂ) * Complex.exp ((q1 * β : ℝ) : ℂ) ≠ 0) :
    finiteGibbsExpectation energy β (C1.comp Cj) =
      c1j / (1 - (s.zetaInt : ℂ) * Complex.exp ((q1 * β : ℝ) : ℂ)) :=
  finiteGibbsExpectation_comp_eq_div_of_zetaCommutator energy β q1 (s.zetaInt : ℂ) c1j C1 Cj hC1
    hcomm hne

end Common
end SecondQuantization
