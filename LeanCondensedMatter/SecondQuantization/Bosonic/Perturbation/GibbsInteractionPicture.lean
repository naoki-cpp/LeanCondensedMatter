import LeanCondensedMatter.SecondQuantization.Bosonic.ImaginaryTime.ImaginaryTimeEvolution
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.ConvergenceAwareGibbs
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.DiagonalEvolution

set_option linter.style.header false

/-!
# Free Gibbs summability and interaction-picture evolution

Free interaction-picture conjugation leaves diagonal free-Gibbs numerators unchanged because the
two diagonal evolution factors cancel on the same occupation state.

This module records the resulting summability and expectation invariance on the genuinely infinite
bosonic occupation space, without a finite occupation-basis assumption.
-/

namespace SecondQuantization
namespace Bosonic

noncomputable section

variable {Mode : Type*} [Fintype Mode]

omit [Fintype Mode] in
/-- The diagonal free-Gibbs numerator is invariant under interaction-picture conjugation. -/
theorem matrixCoeff_freeGibbs_interactionPicture_self
    (ε : Mode → ℝ) (β σ : ℝ) (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode)
    (n : Occupation Mode) :
    Common.matrixCoeff
        ((imaginaryTimeEvolveFree ε (-β)).comp (interactionPicture ε V σ)) n n =
      Common.matrixCoeff ((imaginaryTimeEvolveFree ε (-β)).comp V) n n := by
  simp only [imaginaryTimeEvolveFree]
  rw [Common.matrixCoeff_diagonalEvolution_comp,
    Common.matrixCoeff_diagonalEvolution_comp, interactionPicture,
    Common.matrixCoeff_interactionPicture]
  simp

omit [Fintype Mode] in
/-- Free Gibbs summability is preserved by free interaction-picture conjugation. -/
theorem freeGibbsSummable_interactionPicture_iff
    (ε : Mode → ℝ) (β σ : ℝ) (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode) :
    freeGibbsSummable ε β (interactionPicture ε V σ) ↔ freeGibbsSummable ε β V := by
  unfold freeGibbsSummable
  constructor <;> intro h
  · exact h.congr fun n => matrixCoeff_freeGibbs_interactionPicture_self ε β σ V n
  · exact h.congr fun n => (matrixCoeff_freeGibbs_interactionPicture_self ε β σ V n).symm

omit [Fintype Mode] in
/-- The normalized free Gibbs expectation is invariant under free interaction-picture conjugation.
This equality is pointwise on the diagonal numerator, so no extra summability hypothesis is needed
for the equality itself. -/
theorem freeGibbsExpectation_interactionPicture
    (ε : Mode → ℝ) (β σ : ℝ) (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode) :
    freeGibbsExpectation ε β (interactionPicture ε V σ) = freeGibbsExpectation ε β V := by
  unfold freeGibbsExpectation Common.tsumTrace
  congr 1
  exact tsum_congr fun n => matrixCoeff_freeGibbs_interactionPicture_self ε β σ V n


end
end Bosonic
end SecondQuantization
