import LeanCondensedMatter.SecondQuantization.Bosonic.ImaginaryTime.ImaginaryTimeEvolution
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.ConvergenceAwareGibbs
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.DiagonalEvolution

set_option linter.style.header false

/-!
# Free Gibbs summability and interaction-picture evolution

Physical-H interaction-picture conjugation leaves grand-canonical Gibbs numerators unchanged.
The physical evolution uses the dispersion `ε`, while the Gibbs weights use `ε - μ`;
the two interaction-picture factors cancel on each occupation diagonal.

This module records the resulting summability and expectation invariance on the genuinely infinite
bosonic occupation space, without a finite occupation-basis assumption.
-/

namespace SecondQuantization
namespace Bosonic

noncomputable section

variable {Mode : Type*} [Fintype Mode]

omit [Fintype Mode] in
/-- Conjugation by the physical interaction-picture operator preserves diagonal matrix
coefficients after multiplication by any independent diagonal thermal weight. -/
theorem matrixCoeff_diagonalGibbs_interactionPicture_self
    (ε ξ : Mode → ℝ) (β σ : ℝ) (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode)
    (n : Occupation Mode) :
    Common.matrixCoeff
        ((imaginaryTimeEvolveFree ξ (-β)).comp (interactionPicture ε V σ)) n n =
      Common.matrixCoeff ((imaginaryTimeEvolveFree ξ (-β)).comp V) n n := by
  simp only [imaginaryTimeEvolveFree]
  rw [Common.matrixCoeff_diagonalEvolution_comp,
    Common.matrixCoeff_diagonalEvolution_comp, interactionPicture,
    Common.matrixCoeff_interactionPicture]
  simp

omit [Fintype Mode] in
/-- Grand-canonical Gibbs summability is invariant under physical-H
interaction-picture conjugation, for arbitrary chemical potential. -/
theorem grandCanonicalGibbsSummable_interactionPicture_iff
    (ε : Mode → ℝ) (β μ σ : ℝ) (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode) :
    freeGibbsSummable (fun i => ε i - μ) β (interactionPicture ε V σ) ↔
      freeGibbsSummable (fun i => ε i - μ) β V := by
  unfold freeGibbsSummable
  constructor <;> intro h
  · exact h.congr fun n => matrixCoeff_diagonalGibbs_interactionPicture_self ε (fun i => ε i - μ) β σ V n
  · exact h.congr fun n => (matrixCoeff_diagonalGibbs_interactionPicture_self ε (fun i => ε i - μ) β σ V n).symm

omit [Fintype Mode] in
/-- Grand-canonical Gibbs expectation is invariant under physical-H interaction-picture
conjugation. The identity holds pointwise for the diagonal numerators, without a separate
summability assumption; a normalized-state interpretation still requires convergence. -/
theorem grandCanonicalGibbsExpectation_interactionPicture
    (ε : Mode → ℝ) (β μ σ : ℝ) (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode) :
    freeGibbsExpectation (fun i => ε i - μ) β (interactionPicture ε V σ) =
      freeGibbsExpectation (fun i => ε i - μ) β V := by
  unfold freeGibbsExpectation Common.tsumTrace
  congr 1
  exact tsum_congr fun n => matrixCoeff_diagonalGibbs_interactionPicture_self ε (fun i => ε i - μ) β σ V n


end
end Bosonic
end SecondQuantization
