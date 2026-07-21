import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.GibbsExpectation.TwoPoint
import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.FourPointReduction

set_option linter.style.header false

/-!
# The normalized 4-point Bloch–de Dominicis identities

Divides `BlochDeDominicis/FourPointReduction.lean`'s un-normalized 4-point first-operator
reduction through by the genuine partition function, then rewrites its coefficients as normalized
2-point values (via `TwoPoint.lean`) to reach the genuine 4-point *expansion* — the physics
reference notes' own 4-point example.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*} [Fintype Config]

/-- **The normalized 4-point Bloch–de Dominicis *first-operator reduction***, dividing
`FourPointReduction.lean`'s un-normalized `(1 - ζ³w₁) Tr[e^{-βH₀}(C₁C₂C₃C₄)] = c₁₂
Tr[e^{-βH₀}(C₃C₄)] + ζc₁₃ Tr[e^{-βH₀}(C₂C₄)] + ζ²c₁₄ Tr[e^{-βH₀}(C₂C₃)]` through by the genuine
partition function: `⟨C₁C₂C₃C₄⟩ = (c₁₂⟨C₃C₄⟩ + ζc₁₃⟨C₂C₄⟩ + ζ²c₁₄⟨C₂C₃⟩) / (1 - ζ³w₁)`. **Still not
the genuine 4-point *expansion*** (`⟨C₁C₂⟩⟨C₃C₄⟩ + ζ⟨C₁C₃⟩⟨C₂C₄⟩ + ⟨C₁C₄⟩⟨C₂C₃⟩`, a sum of
*products* of normalized 2-point numbers, `gibbsExpectation_four_point` below) — the remaining
`⟨C₃C₄⟩`/`⟨C₂C₄⟩`/`⟨C₂C₃⟩` terms are already normalized 2-point numbers and need no further
reduction; what's missing is only rewriting the *coefficients* `c₁ⱼ/(1-ζw₁)` as `⟨C₁Cⱼ⟩` (via
`gibbsExpectation_comp_eq_div_of_zetaCommutator`, which needs exactly `hC1`/`hcomm1j` — already
supplied here, not new hypotheses on `C₂`/`C₃`/`C₄`) and using `ζ² = 1` (true for `ζ = ±1`, i.e.
`Statistics.zetaInt`) to turn `ζ³` into `ζ` and the trailing `ζ²c₁₄` coefficient into a bare `1`. -/
theorem gibbsExpectation_comp_comp_comp_eq_div_of_zetaCommutator (energy : Config → ℝ) (β q1 : ℝ)
    (ζ c12 c13 c14 : ℂ) (C1 C2 C3 C4 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hC1 : heisenbergEvolve energy (-β) C1 = Complex.exp ((q1 * (-β) : ℝ) : ℂ) • C1)
    (hcomm12 : C1.comp C2 - ζ • (C2.comp C1) =
      c12 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hcomm13 : C1.comp C3 - ζ • (C3.comp C1) =
      c13 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hcomm14 : C1.comp C4 - ζ • (C4.comp C1) =
      c14 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hZ : traceFock (diagonalEvolution energy (-β)) ≠ 0)
    (hne : (1 : ℂ) - ζ ^ 3 * Complex.exp ((q1 * β : ℝ) : ℂ) ≠ 0) :
    gibbsExpectation energy β (C1.comp (C2.comp (C3.comp C4))) =
      (c12 * gibbsExpectation energy β (C3.comp C4) +
          ζ * c13 * gibbsExpectation energy β (C2.comp C4) +
          ζ ^ 2 * c14 * gibbsExpectation energy β (C2.comp C3)) /
        (1 - ζ ^ 3 * Complex.exp ((q1 * β : ℝ) : ℂ)) := by
  have h := traceFock_diagonalEvolution_comp_four_point_reduction energy β q1 ζ c12 c13 c14
    C1 C2 C3 C4 hC1 hcomm12 hcomm13 hcomm14
  have hne' : (1 : ℂ) - ζ ^ 3 * Complex.exp ((β * q1 : ℝ) : ℂ) ≠ 0 := by
    rwa [mul_comm β q1]
  simp only [gibbsExpectation_eq_normalizedWeightedDiagonal, normalizedWeightedDiagonal,
    ← traceFock_diagonalEvolution_comp_eq_weightedTrace, ← traceFock_diagonalEvolution_eq_weightSum]
  field_simp [hne']
  linear_combination (norm := ring_nf) h

/-- **The genuine normalized 4-point Bloch–de Dominicis expansion**: `⟨C₁C₂C₃C₄⟩ = ⟨C₁C₂⟩⟨C₃C₄⟩ +
ζ⟨C₁C₃⟩⟨C₂C₄⟩ + ⟨C₁C₄⟩⟨C₂C₃⟩` (the physics reference notes' `quantum-statistical-mechanics.tex`
example, `for ζ = ±1`) — a product of *normalized 2-point numbers*, obtained from
`gibbsExpectation_comp_comp_comp_eq_div_of_zetaCommutator` purely by rewriting each coefficient
`c₁ⱼ/(1-ζw₁)` as `⟨C₁Cⱼ⟩` via `gibbsExpectation_comp_eq_div_of_zetaCommutator` (needing no new
hypotheses on `C₂`/`C₃`/`C₄` — only `hC1`/`hcomm1j`, already present) and using `hζ2 : ζ² = 1` to
collapse `ζ³` to `ζ` and the trailing `ζ²c₁₄` coefficient to `1`. -/
theorem gibbsExpectation_four_point (energy : Config → ℝ) (β q1 : ℝ) (ζ c12 c13 c14 : ℂ)
    (C1 C2 C3 C4 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hC1 : heisenbergEvolve energy (-β) C1 = Complex.exp ((q1 * (-β) : ℝ) : ℂ) • C1)
    (hcomm12 : C1.comp C2 - ζ • (C2.comp C1) =
      c12 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hcomm13 : C1.comp C3 - ζ • (C3.comp C1) =
      c13 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hcomm14 : C1.comp C4 - ζ • (C4.comp C1) =
      c14 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hζ2 : ζ ^ 2 = 1)
    (hZ : traceFock (diagonalEvolution energy (-β)) ≠ 0)
    (hne : (1 : ℂ) - ζ * Complex.exp ((q1 * β : ℝ) : ℂ) ≠ 0) :
    gibbsExpectation energy β (C1.comp (C2.comp (C3.comp C4))) =
      gibbsExpectation energy β (C1.comp C2) * gibbsExpectation energy β (C3.comp C4) +
        ζ * gibbsExpectation energy β (C1.comp C3) * gibbsExpectation energy β (C2.comp C4) +
        gibbsExpectation energy β (C1.comp C4) * gibbsExpectation energy β (C2.comp C3) := by
  have hζ3 : ζ ^ 3 = ζ := by
    have h32 : ζ ^ 3 = ζ ^ 2 * ζ := by ring
    rw [h32, hζ2, one_mul]
  have hne3 : (1 : ℂ) - ζ ^ 3 * Complex.exp ((q1 * β : ℝ) : ℂ) ≠ 0 := by rwa [hζ3]
  have h4 := gibbsExpectation_comp_comp_comp_eq_div_of_zetaCommutator energy β q1 ζ c12 c13 c14
    C1 C2 C3 C4 hC1 hcomm12 hcomm13 hcomm14 hZ hne3
  rw [hζ3, hζ2] at h4
  have h12 := gibbsExpectation_comp_eq_div_of_zetaCommutator energy β q1 ζ c12 C1 C2 hC1 hcomm12
    hZ hne
  have h13 := gibbsExpectation_comp_eq_div_of_zetaCommutator energy β q1 ζ c13 C1 C3 hC1 hcomm13
    hZ hne
  have h14 := gibbsExpectation_comp_eq_div_of_zetaCommutator energy β q1 ζ c14 C1 C4 hC1 hcomm14
    hZ hne
  rw [h4, h12, h13, h14]
  field_simp

end Common
end SecondQuantization
