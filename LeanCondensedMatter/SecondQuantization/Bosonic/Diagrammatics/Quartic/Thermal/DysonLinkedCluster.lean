import LeanCondensedMatter.Analysis.PowerSeries.Cumulant
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic.Thermal.DysonExpansion.Moment
import LeanCondensedMatter.SecondQuantization.Bosonic.Perturbation.DysonGibbsSeries

set_option linter.style.header false

/-!
# Bosonic quartic Dyson linked-cluster theorem

The physical convergence-aware bosonic Dyson coefficients were identified with the object moments
of the multiplicative time-integrated quartic-diagram weight. Packaging those coefficients as the
unit-constant `grandCanonicalGibbsDysonSeries` lets the generic formal-log/connected-decomposition theorem
identify its logarithm coefficient with the connected physical Dyson diagrams.

This is a formal, coefficientwise theorem. No analyticity of an interacting bosonic partition
function is assumed or asserted.
-/

namespace SecondQuantization
namespace Bosonic

noncomputable section

variable {Mode : Type*} [Fintype Mode]

/-- Bosonic quartic Dyson Linked Cluster Theorem for the physical convergence-aware Gibbs
coefficients. -/
theorem factorial_mul_coeff_grandCanonicalGibbsDysonFormalLog_eq_sum_connectedDysonThermalAmplitude
    (ε : Mode → ℝ) (β μ : ℝ) (hpos : ∀ i, 0 < β * (ε i - μ))
    (g : QuarticVertexLabel Mode → ℂ) (n : ℕ) (hn : n ≠ 0) :
    (n.factorial : ℂ) *
        PowerSeries.coeff n
          (grandCanonicalGibbsDysonFormalLog ε β μ (quarticInteraction g)) =
      ∑ d : Common.ConnectedQuarticDiagram (QuarticVertexLabel Mode) n Finset.univ,
        QuarticDiagram.dysonThermalAmplitude ε β μ g d.1 β := by
  let W := quarticDysonThermalDiagramMultiplicativeWeight (N := n) ε β μ g β
  have hZ :
      PowerSeries.constantCoeff
          (grandCanonicalGibbsDysonSeries ε β μ (quarticInteraction g)) = 1 :=
    constantCoeff_grandCanonicalGibbsDysonSeries ε β μ hpos (quarticInteraction g)
  have hMoment :
      Combinatorics.powerSeriesMomentSetFunction (α := Fin n)
          (grandCanonicalGibbsDysonSeries ε β μ (quarticInteraction g)) hZ =
        W.normalizedObjectMoment := by
    simpa only [W] using
      (powerSeriesMomentSetFunction_grandCanonicalGibbsDysonSeries_eq_dysonThermalObjectMoment
        (N := n) ε β μ hpos g hZ)
  have huniv : (Finset.univ : Finset (Fin n)) ≠ ∅ :=
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩).ne_empty
  calc
    (n.factorial : ℂ) *
        PowerSeries.coeff n
          (grandCanonicalGibbsDysonFormalLog ε β μ (quarticInteraction g)) =
        W.connectedContribution (Finset.univ : Finset (Fin n)) := by
      simpa [grandCanonicalGibbsDysonFormalLog] using
        (Combinatorics.factorial_mul_coeff_logOf_eq_connectedContribution
          hZ W hMoment huniv)
    _ = ∑ d : Common.ConnectedQuarticDiagram (QuarticVertexLabel Mode) n Finset.univ,
          QuarticDiagram.dysonThermalAmplitude ε β μ g d.1 β := rfl

end
end Bosonic
end SecondQuantization
