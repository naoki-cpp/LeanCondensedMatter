import LeanCondensedMatter.SecondQuantization.Bosonic.Perturbation.GibbsInteractionPicture
import LeanCondensedMatter.SecondQuantization.Bosonic.Perturbation.QuarticVertexBound
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BoltzmannWeightSummable
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.DiagonalCompositionMatrixCoeff

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Free-Gibbs summability of bosonic quartic interactions

A single ordered quartic vertex has diagonal matrix coefficients bounded by `(N + 2)^2`, where `N`
is the total occupation number.  The free Boltzmann factor turns this polynomial growth into a
summable sequence.  Finite linear closure of the convergence-aware Gibbs domain then promotes the
single-vertex result to finitely supported quartic interactions and, for finite mode types, to the
all-label quartic interaction.
-/

namespace SecondQuantization
namespace Bosonic

open Common

noncomputable section

variable {Mode : Type*} [Fintype Mode]

/-- A single ordered bosonic quartic vertex has a summable free-Gibbs numerator under the usual
positive one-mode Boltzmann exponents. -/
theorem freeGibbsSummable_quarticVertexOperator
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (q : QuarticVertexLabel Mode) :
    freeGibbsSummable ε β (quarticVertexOperator q) := by
  unfold freeGibbsSummable
  have hN2 := summable_particleNumber_total_sq_boltzmannWeight ε β hpos
  have hW := summable_boltzmannWeight ε β hpos
  have hmajorant : Summable (fun n : Occupation Mode =>
      2 * ((particleNumber n : ℝ) ^ 2 * boltzmannWeight ε β n) +
        8 * boltzmannWeight ε β n) :=
    (hN2.mul_left (2 : ℝ)).add (hW.mul_left (8 : ℝ))
  apply hmajorant.of_norm_bounded
  intro n
  simp only [imaginaryTimeEvolveFree]
  rw [Common.matrixCoeff_diagonalEvolution_comp, norm_mul, Complex.norm_exp]
  have hq := norm_matrixCoeff_quarticVertexOperator_le q n
  have hw : 0 ≤ boltzmannWeight ε β n := Real.exp_nonneg _
  have hpoly :
      ((particleNumber n : ℝ) + 2) ^ 2 ≤ 2 * (particleNumber n : ℝ) ^ 2 + 8 := by
    nlinarith [sq_nonneg ((particleNumber n : ℝ) - 2)]
  change boltzmannWeight ε β n * ‖Common.matrixCoeff (quarticVertexOperator q) n n‖ ≤ _
  calc
    boltzmannWeight ε β n * ‖Common.matrixCoeff (quarticVertexOperator q) n n‖ ≤
        boltzmannWeight ε β n * ((particleNumber n : ℝ) + 2) ^ 2 :=
      mul_le_mul_of_nonneg_left hq hw
    _ ≤ boltzmannWeight ε β n * (2 * (particleNumber n : ℝ) ^ 2 + 8) :=
      mul_le_mul_of_nonneg_left hpoly hw
    _ = 2 * ((particleNumber n : ℝ) ^ 2 * boltzmannWeight ε β n) +
        8 * boltzmannWeight ε β n := by ring

/-- A single ordered quartic vertex belongs to the explicit free-Gibbs domain. -/
theorem quarticVertexOperator_mem_freeGibbsDomain
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (q : QuarticVertexLabel Mode) :
    quarticVertexOperator q ∈ freeGibbsDomain ε β :=
  freeGibbsSummable_quarticVertexOperator ε β hpos q

/-- Every finitely supported bosonic quartic interaction belongs to the free-Gibbs domain. -/
theorem quarticInteractionOn_mem_freeGibbsDomain
    (support : Finset (QuarticVertexLabel Mode))
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (g : QuarticVertexLabel Mode → ℂ) :
    quarticInteractionOn support g ∈ freeGibbsDomain ε β := by
  classical
  change (∑ q ∈ support, g q • quarticVertexOperator q) ∈ freeGibbsDomain ε β
  exact Submodule.sum_mem (freeGibbsDomain ε β) fun q hq =>
    (freeGibbsDomain ε β).smul_mem (g q)
      (quarticVertexOperator_mem_freeGibbsDomain ε β hpos q)

/-- On a finite mode type, the all-label bosonic quartic interaction belongs to the free-Gibbs
domain. -/
theorem quarticInteraction_mem_freeGibbsDomain
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (g : QuarticVertexLabel Mode → ℂ) :
    quarticInteraction g ∈ freeGibbsDomain ε β := by
  simpa [quarticInteraction, quarticInteractionOn, Common.quarticInteraction] using
    (quarticInteractionOn_mem_freeGibbsDomain
      (support := (Finset.univ : Finset (QuarticVertexLabel Mode))) ε β hpos g)

end
end Bosonic
end SecondQuantization
