import LeanCondensedMatter.Analysis.PowerSeries.Cumulant
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic.Thermal.DysonExpansion
import LeanCondensedMatter.SecondQuantization.Bosonic.Perturbation.DysonGibbsSeries

set_option linter.style.header false

/-!
# Bosonic quartic Dyson linked-cluster theorem

The physical convergence-aware bosonic Dyson coefficients were identified with the object moments
of the multiplicative time-integrated quartic-diagram weight. Packaging those coefficients as the
unit-constant `freeGibbsDysonSeries` lets the generic formal-log/connected-decomposition theorem
identify its logarithm coefficient with the connected physical Dyson diagrams.

This is a formal, coefficientwise theorem. No analyticity of an interacting bosonic partition
function is assumed or asserted.
-/

namespace SecondQuantization
namespace Bosonic

noncomputable section

variable {Mode : Type*} [Fintype Mode]

private theorem fin_univ_ne_empty {n : ℕ} (hn : n ≠ 0) :
    (Finset.univ : Finset (Fin n)) ≠ ∅ := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  intro h
  have hx : (⟨0, hnpos⟩ : Fin n) ∈ (Finset.univ : Finset (Fin n)) :=
    Finset.mem_univ _
  rw [h] at hx
  simpa using hx

/-- Bosonic quartic Dyson Linked Cluster Theorem for the physical convergence-aware Gibbs
coefficients. -/
theorem factorial_mul_coeff_freeGibbsDysonFormalLog_eq_sum_connectedDysonThermalAmplitude
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (g : QuarticVertexLabel Mode → ℂ) (n : ℕ) (hn : n ≠ 0) :
    (n.factorial : ℂ) *
        PowerSeries.coeff n
          (freeGibbsDysonFormalLog ε β (quarticInteraction g)) =
      ∑ d : Common.ConnectedQuarticDiagram (QuarticVertexLabel Mode) n Finset.univ,
        QuarticDiagram.dysonThermalAmplitude ε β g d.1 β := by
  let W := quarticDysonThermalDiagramMultiplicativeWeight (N := n) ε β g β
  have hZ :
      PowerSeries.constantCoeff
          (freeGibbsDysonSeries ε β (quarticInteraction g)) = 1 :=
    constantCoeff_freeGibbsDysonSeries ε β hpos (quarticInteraction g)
  have hMoment :
      Combinatorics.powerSeriesMomentSetFunction (α := Fin n)
          (freeGibbsDysonSeries ε β (quarticInteraction g)) hZ =
        W.normalizedObjectMoment := by
    apply Combinatorics.NormalizedSetFunction.ext
    intro S
    simp only [Combinatorics.powerSeriesMomentSetFunction,
      Combinatorics.powerSeriesMomentCoeff,
      Combinatorics.MultiplicativeWeight.normalizedObjectMoment_apply]
    rw [coeff_freeGibbsDysonSeries]
    exact (quarticDysonThermalMoment_eq_factorial_mul_freeGibbsDysonCoeff
      ε β hpos g β S).symm
  have huniv : (Finset.univ : Finset (Fin n)) ≠ ∅ := fin_univ_ne_empty hn
  calc
    (n.factorial : ℂ) *
        PowerSeries.coeff n
          (freeGibbsDysonFormalLog ε β (quarticInteraction g)) =
        W.connectedContribution (Finset.univ : Finset (Fin n)) := by
      simpa [freeGibbsDysonFormalLog] using
        (Combinatorics.factorial_mul_coeff_logOf_eq_connectedContribution
          hZ W hMoment huniv)
    _ = ∑ d : Common.ConnectedQuarticDiagram (QuarticVertexLabel Mode) n Finset.univ,
          QuarticDiagram.dysonThermalAmplitude ε β g d.1 β := rfl

end
end Bosonic
end SecondQuantization
