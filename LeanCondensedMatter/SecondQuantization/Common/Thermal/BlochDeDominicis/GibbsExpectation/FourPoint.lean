import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.GibbsExpectation.TwoPoint
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized.PeelFirstTrace

set_option linter.style.header false

/-!
# The normalized 4-point Bloch–de Dominicis identities

Specializes the generic unnormalized peel-first trace identity to three remaining operators, divides
through by the genuine partition function, then rewrites its coefficients as normalized 2-point
values (via `TwoPoint.lean`) to reach the genuine 4-point expansion.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*} [Fintype Config] [Nonempty Config]

/-- The normalized 4-point first-operator reduction. -/
theorem finiteGibbsExpectation_comp_comp_comp_eq_div_of_zetaCommutator
    (energy : Config → ℝ) (β q1 : ℝ)
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
    finiteGibbsExpectation energy β (C1.comp (C2.comp (C3.comp C4))) =
      (c12 * finiteGibbsExpectation energy β (C3.comp C4) +
          ζ * c13 * finiteGibbsExpectation energy β (C2.comp C4) +
          ζ ^ 2 * c14 * finiteGibbsExpectation energy β (C2.comp C3)) /
        (1 - ζ ^ 3 * Complex.exp ((q1 * β : ℝ) : ℂ)) := by
  have hmem : ∀ p ∈ [(C2, c12), (C3, c13), (C4, c14)], zetaCommutator ζ C1 p.1 =
      p.2 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) := by
    intro p hp
    fin_cases hp
    · exact hcomm12
    · exact hcomm13
    · exact hcomm14
  have hz : traceFock (0 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) = 0 := by
    simp [traceFock, matrixCoeff]
  have h := traceFock_diagonalEvolution_comp_peel energy β q1 ζ C1
    [(C2, c12), (C3, c13), (C4, c14)] hC1 hmem
  simp only [prodComp, peelSum, List.map_cons, List.map_nil, List.length_cons, List.length_nil,
    LinearMap.comp_id, LinearMap.comp_zero, LinearMap.comp_add, LinearMap.comp_smul,
    traceFock_add, traceFock_smul, hz, mul_zero] at h
  have hne' : (1 : ℂ) - ζ ^ 3 * Complex.exp ((β * q1 : ℝ) : ℂ) ≠ 0 := by
    rwa [mul_comm β q1]
  simp only [finiteGibbsExpectation_eq_trace_div]
  field_simp [hZ, hne']
  linear_combination (norm := ring_nf) h

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
    (hZ : traceFock (diagonalEvolution energy (-β)) ≠ 0)
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
  have hne3 : (1 : ℂ) - ζ ^ 3 * Complex.exp ((q1 * β : ℝ) : ℂ) ≠ 0 := by rwa [hζ3]
  have h4 := finiteGibbsExpectation_comp_comp_comp_eq_div_of_zetaCommutator energy β q1 ζ c12
    c13 c14 C1 C2 C3 C4 hC1 hcomm12 hcomm13 hcomm14 hZ hne3
  rw [hζ3, hζ2] at h4
  have h12 := finiteGibbsExpectation_comp_eq_div_of_zetaCommutator energy β q1 ζ c12 C1 C2 hC1
    hcomm12 hZ hne
  have h13 := finiteGibbsExpectation_comp_eq_div_of_zetaCommutator energy β q1 ζ c13 C1 C3 hC1
    hcomm13 hZ hne
  have h14 := finiteGibbsExpectation_comp_eq_div_of_zetaCommutator energy β q1 ζ c14 C1 C4 hC1
    hcomm14 hZ hne
  rw [h4, h12, h13, h14]
  field_simp

end Common
end SecondQuantization
