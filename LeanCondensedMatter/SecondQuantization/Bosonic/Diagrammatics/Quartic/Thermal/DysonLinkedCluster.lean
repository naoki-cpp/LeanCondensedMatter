import LeanCondensedMatter.Analysis.PowerSeries.Cumulant
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic.Thermal.DysonExpansion.Factorization
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic.Thermal.DysonExpansion.Pairing
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
theorem factorial_mul_coeff_logOf_grandCanonicalGibbsDysonSeries_eq_sum_connectedDysonThermalAmplitude
    (ε : Mode → ℝ) (β μ : ℝ) (hpos : ∀ i, 0 < β * (ε i - μ))
    (g : QuarticVertexLabel Mode → ℂ) (n : ℕ) (hn : n ≠ 0) :
    (n.factorial : ℂ) *
        PowerSeries.coeff n
          (PowerSeries.logOf (grandCanonicalGibbsDysonSeries ε β μ (quarticInteraction g))) =
      ∑ d : Common.ConnectedQuarticDiagram (QuarticVertexLabel Mode) n Finset.univ,
        QuarticDiagram.dysonThermalAmplitude ε β μ g d.1 β := by
  let W : Combinatorics.MultiplicativeWeight
      (Common.quarticDiagramConnectedDecomposition (QuarticVertexLabel Mode) n) ℂ :=
    Common.QuarticDiagram.multiplicativeWeight
      (N := n)
      (fun d => QuarticDiagram.dysonThermalAmplitude ε β μ g d β)
      (fun d => by
        simpa only [Common.QuarticDiagram.restrictComponentConnected] using
          QuarticDiagram.dysonThermalAmplitude_eq_prod_components ε β μ g d β)
  have hZ :
      PowerSeries.constantCoeff
          (grandCanonicalGibbsDysonSeries ε β μ (quarticInteraction g)) = 1 :=
    constantCoeff_grandCanonicalGibbsDysonSeries ε β μ hpos (quarticInteraction g)
  have hMoment :
      Combinatorics.powerSeriesMomentSetFunction (α := Fin n)
          (grandCanonicalGibbsDysonSeries ε β μ (quarticInteraction g)) hZ =
        W.normalizedObjectMoment := by
    rw [Combinatorics.powerSeriesMomentSetFunction_eq_iff]
    intro S
    simp only [Combinatorics.powerSeriesMomentCoeff, coeff_grandCanonicalGibbsDysonSeries]
    change
      (S.card.factorial : ℂ) *
          grandCanonicalGibbsDysonCoeff ε β μ (quarticInteraction g) S.card β =
        ∑ d : Common.QuarticDiagram (QuarticVertexLabel Mode) n S,
          QuarticDiagram.dysonThermalAmplitude ε β μ g d β
    exact factorial_mul_grandCanonicalGibbsDysonCoeff_quarticInteraction_eq_sum_dysonThermalAmplitude
      ε β μ hpos g S β
  have huniv : (Finset.univ : Finset (Fin n)) ≠ ∅ :=
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩).ne_empty
  calc
    (n.factorial : ℂ) *
        PowerSeries.coeff n
          (PowerSeries.logOf (grandCanonicalGibbsDysonSeries ε β μ (quarticInteraction g))) =
        W.connectedContribution (Finset.univ : Finset (Fin n)) := by
      simpa using
        (Combinatorics.factorial_mul_coeff_logOf_eq_connectedContribution
          hZ W hMoment huniv)
    _ = ∑ d : Common.ConnectedQuarticDiagram (QuarticVertexLabel Mode) n Finset.univ,
          QuarticDiagram.dysonThermalAmplitude ε β μ g d.1 β := rfl

end
end Bosonic
end SecondQuantization
