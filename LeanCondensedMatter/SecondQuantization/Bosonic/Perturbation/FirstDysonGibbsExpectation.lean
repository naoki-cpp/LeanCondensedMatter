import LeanCondensedMatter.SecondQuantization.Bosonic.Perturbation.FirstDysonGibbsSummable

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Free-Gibbs expectation of the first Dyson coefficient

The first Dyson coefficient has a free-Gibbs diagonal numerator equal pointwise to the bare
interaction numerator times the signed interval length. This lets us evaluate its normalized Gibbs
expectation directly, without first interchanging an infinite occupation sum with an interval
integral. The same identity supplies the order-zero `expectation_succ` clause of the explicit Dyson
analytic boundary.
-/

namespace SecondQuantization
namespace Bosonic

noncomputable section

variable {Mode : Type*} [Fintype Mode]

omit [Fintype Mode] in
private theorem expectation_matrixCoeff_dysonCoeff_one_self
    (ε : Mode → ℝ) (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode)
    (t : ℝ) (n : Occupation Mode) :
    Common.matrixCoeff (Common.dysonCoeff (freeEigenvalue ε) V 1 t) n n =
      -(t : ℂ) * Common.matrixCoeff V n n := by
  change Common.dysonCoeff (freeEigenvalue ε) V 1 t (Common.basisState n) n = _
  rw [show 1 = 0 + 1 by omega, Common.dysonCoeff_succ_basisState_apply]
  simp only [Common.dysonCoeff_zero, LinearMap.id_apply]
  have hdiag : ∀ σ : ℝ,
      Common.interactionPicture (freeEigenvalue ε) V σ (Common.basisState n) n =
        Common.matrixCoeff V n n := by
    intro σ
    change Common.matrixCoeff
      (Common.interactionPicture (freeEigenvalue ε) V σ) n n = Common.matrixCoeff V n n
    rw [Common.matrixCoeff_interactionPicture]
    norm_num
  simp_rw [hdiag]
  rw [intervalIntegral.integral_const]
  simp only [sub_zero]
  change -((t : ℂ) * Common.matrixCoeff V n n) = _
  exact (neg_mul (t : ℂ) (Common.matrixCoeff V n n)).symm

omit [Fintype Mode] in
private theorem expectation_matrixCoeff_freeGibbs_dysonCoeff_one_self
    (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode)
    (t : ℝ) (n : Occupation Mode) :
    Common.matrixCoeff
        ((imaginaryTimeEvolveFree ε (-β)).comp
          (Common.dysonCoeff (freeEigenvalue ε) V 1 t)) n n =
      -(t : ℂ) *
        Common.matrixCoeff ((imaginaryTimeEvolveFree ε (-β)).comp V) n n := by
  simp only [imaginaryTimeEvolveFree]
  rw [Common.matrixCoeff_diagonalEvolution_comp,
    expectation_matrixCoeff_dysonCoeff_one_self,
    Common.matrixCoeff_diagonalEvolution_comp]
  ring

omit [Fintype Mode] in
/-- The normalized free-Gibbs expectation of the first Dyson coefficient is the bare interaction
expectation multiplied by the signed interval length. -/
private theorem freeGibbsExpectation_dysonCoeff_one
    (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode) (t : ℝ) :
    freeGibbsExpectation ε β (Common.dysonCoeff (freeEigenvalue ε) V 1 t) =
      -(t : ℂ) * freeGibbsExpectation ε β V := by
  rw [← freeGibbsExpectation_smul ε β (-(t : ℂ)) V]
  unfold freeGibbsExpectation Common.tsumTrace
  congr 1
  apply tsum_congr
  intro n
  rw [expectation_matrixCoeff_freeGibbs_dysonCoeff_one_self]
  simp only [LinearMap.comp_smul, ← Common.matrixCoeffLinear_apply, map_smul, smul_eq_mul]

omit [Fintype Mode] in
/-- At Dyson order zero, the Gibbs expectation satisfies the recursive interval formula directly.
No infinite-sum/integral interchange hypothesis is required because the integrand expectation is
constant after free interaction-picture conjugation. -/
theorem freeGibbsExpectation_dysonCoeff_one_eq_intervalIntegral
    (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode) (t : ℝ) :
    freeGibbsExpectation ε β (Common.dysonCoeff (freeEigenvalue ε) V 1 t) =
      -∫ σ in (0 : ℝ)..t,
        freeGibbsExpectation ε β
          ((interactionPicture ε V σ).comp
            (Common.dysonCoeff (freeEigenvalue ε) V 0 σ)) := by
  rw [freeGibbsExpectation_dysonCoeff_one]
  simp_rw [Common.dysonCoeff_zero, LinearMap.comp_id,
    freeGibbsExpectation_interactionPicture]
  rw [intervalIntegral.integral_const]
  simp only [sub_zero]
  change -(t : ℂ) * freeGibbsExpectation ε β V =
    -((t : ℂ) * freeGibbsExpectation ε β V)
  exact neg_mul (t : ℂ) (freeGibbsExpectation ε β V)

end
end Bosonic
end SecondQuantization
