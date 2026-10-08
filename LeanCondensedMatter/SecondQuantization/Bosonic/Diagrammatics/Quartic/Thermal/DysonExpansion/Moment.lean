import LeanCondensedMatter.Analysis.PowerSeries.Moment
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic.Thermal.DysonExpansion.Factorization
import LeanCondensedMatter.SecondQuantization.Bosonic.Perturbation.DysonGibbsSeries

set_option linter.style.header false

/-!
# Bosonic quartic Dyson diagram moments

The convergence-aware physical time-integrated Dyson amplitude defines a multiplicative weight.
Its normalized object moment coincides with the factorial-normalized free-Gibbs Dyson power-series
moment; no separate diagram-specific normalized moment wrapper is needed.
-/

namespace SecondQuantization
namespace Bosonic

open Common Combinatorics

noncomputable section

variable {Mode : Type*} [Finite Mode] [Fintype Mode]

/-- The physical time-integrated bosonic quartic Dyson amplitude as a multiplicative diagram
weight on the connected decomposition. -/
noncomputable def quarticDysonThermalDiagramMultiplicativeWeight
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) (t : ℝ) {N : ℕ} :
    Combinatorics.MultiplicativeWeight
      (Common.quarticDiagramConnectedDecomposition (QuarticVertexLabel Mode) N) ℂ :=
  Common.QuarticDiagram.multiplicativeWeight
    (N := N)
    (fun d => QuarticDiagram.dysonThermalAmplitude ε β g d t)
    (fun d => by
      simpa only [Common.QuarticDiagram.restrictComponentConnected] using
        QuarticDiagram.dysonThermalAmplitude_eq_prod_components ε β g d t)

omit [Finite Mode] in
/-- Factorial-normalized free-Gibbs Dyson series moments are exactly the object moments of the
physical time-integrated quartic Dyson-diagram connected decomposition. -/
theorem powerSeriesMomentSetFunction_freeGibbsDysonSeries_eq_dysonThermalObjectMoment
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (g : QuarticVertexLabel Mode → ℂ) {N : ℕ}
    (hZ :
      PowerSeries.constantCoeff
          (freeGibbsDysonSeries ε β (quarticInteraction g)) = 1) :
    Combinatorics.powerSeriesMomentSetFunction (α := Fin N)
        (freeGibbsDysonSeries ε β (quarticInteraction g)) hZ =
      (quarticDysonThermalDiagramMultiplicativeWeight ε β g β).normalizedObjectMoment := by
  rw [Combinatorics.powerSeriesMomentSetFunction_eq_iff]
  intro S
  simp only [Combinatorics.powerSeriesMomentCoeff, coeff_freeGibbsDysonSeries]
  change
    (S.card.factorial : ℂ) *
        freeGibbsDysonCoeff ε β (quarticInteraction g) S.card β =
      ∑ d : Common.QuarticDiagram (QuarticVertexLabel Mode) N S,
        QuarticDiagram.dysonThermalAmplitude ε β g d β
  exact factorial_mul_freeGibbsDysonCoeff_quarticInteraction_eq_sum_dysonThermalAmplitude
    ε β hpos g S β

end
end Bosonic
end SecondQuantization
