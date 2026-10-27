import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.GibbsExpectation.TwoPoint
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.GibbsExpectation.Peel

set_option linter.style.header false

/-!
# The normalized 4-point Bloch–de Dominicis identity

Derives the 4-point expansion from the general trace peel identity and the normalized 2-point
values. The 3-operator trace specialization is kept local to the proof rather than exposed
as a separate public theorem.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*} [Fintype Config] [Nonempty Config]

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

end Common
end SecondQuantization
