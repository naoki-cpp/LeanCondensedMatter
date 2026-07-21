import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.GibbsExpectation.Core
import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.TwoPoint

set_option linter.style.header false

/-!
# The genuine normalized 2-point Bloch–de Dominicis value

Divides `BlochDeDominicis/TwoPoint.lean`'s un-normalized trace identity through by the genuine
(nonzero) partition function, giving the first genuine, normalized-number Bloch–de Dominicis
statement.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*} [Fintype Config]

/-- **The genuine normalized 2-point Bloch–de Dominicis value**: `⟨C₁Cⱼ⟩ = c₁ⱼ/(1 - ζw₁)`,
dividing `TwoPoint.lean`'s un-normalized `(1 - ζw₁) Tr[e^{-βH₀}(C₁Cⱼ)] = c₁ⱼ Tr[e^{-βH₀}]` through
by the genuine (nonzero) partition function and by the (assumed nonzero) `1 - ζw₁` factor —
matching the physics reference notes' `⟨Ĉ₁Ĉⱼ⟩ = C_{1,j}/(1 - ζw₁)` letter-for-letter rather than
leaving it as an un-divided trace equation. -/
theorem gibbsExpectation_comp_eq_div_of_zetaCommutator (energy : Config → ℝ) (β q1 : ℝ)
    (ζ c1j : ℂ) (C1 Cj : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hC1 : heisenbergEvolve energy (-β) C1 = Complex.exp ((q1 * (-β) : ℝ) : ℂ) • C1)
    (hcomm : C1.comp Cj - ζ • (Cj.comp C1) =
      c1j • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hZ : traceFock (diagonalEvolution energy (-β)) ≠ 0)
    (hne : (1 : ℂ) - ζ * Complex.exp ((q1 * β : ℝ) : ℂ) ≠ 0) :
    gibbsExpectation energy β (C1.comp Cj) =
      c1j / (1 - ζ * Complex.exp ((q1 * β : ℝ) : ℂ)) := by
  have h := traceFock_diagonalEvolution_comp_two_point energy β q1 ζ c1j C1 Cj hC1 hcomm
  rw [gibbsExpectation_eq_normalizedWeightedDiagonal, normalizedWeightedDiagonal,
    ← traceFock_diagonalEvolution_comp_eq_weightedTrace, ← traceFock_diagonalEvolution_eq_weightSum,
    div_eq_div_iff hZ hne]
  linear_combination h

end Common
end SecondQuantization
