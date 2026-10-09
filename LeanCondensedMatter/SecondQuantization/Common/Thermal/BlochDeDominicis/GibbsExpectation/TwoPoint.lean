import LeanCondensedMatter.Analysis.ScalarExchange.Basic
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsCoordinate
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized.PeelFirstTrace
import LeanCondensedMatter.SecondQuantization.Common.Algebra.ExchangeCommutator

set_option linter.style.header false

/-!
# The genuine normalized 2-point Bloch–de Dominicis value

Applies the general trace peel identity to a singleton coefficient-paired tail and divides by
the nonzero partition function to obtain the normalized finite-temperature two-point value.
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
  have h := traceFock_diagonalEvolution_comp_peel energy β q1 ζ C1 [(Cj, c1j)] hC1
    (by simpa using hcomm)
  simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, pow_one, mul_one,
    ScalarExchange.peelSumWithCoefficients, mul_zero, smul_zero, add_zero] at h
  simp only [Module.End.one_eq_id, LinearMap.comp_smul, LinearMap.comp_id,
    map_smul, smul_eq_mul] at h
  have hZ := traceFock_diagonalEvolution_ne_zero energy β
  rw [finiteGibbsExpectation_eq_trace_div, div_eq_div_iff hZ hne]
  linear_combination h

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
