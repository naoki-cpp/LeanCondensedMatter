import LeanCondensedMatter.Analysis.PowerSeries
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Components.ComponentDecompositionEquiv
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.Wick.AmplitudeFactorization
import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonVertexMoment

set_option linter.style.header false

/-!
# Fermionic Dyson linked cluster theorem

The factorial-normalized Dyson moments are identified with the object moments of the multiplicative
quartic Wick-diagram decomposition. The statistics-independent formal power-series/connected-
decomposition theorem then yields the canonical formal Linked Cluster Theorem.
-/

open scoped BigOperators

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {N : ℕ}

private theorem fin_univ_ne_empty {n : ℕ} (hn : n ≠ 0) :
    (Finset.univ : Finset (Fin n)) ≠ ∅ := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  intro h
  have hx : (⟨0, hnpos⟩ : Fin n) ∈ (Finset.univ : Finset (Fin n)) :=
    Finset.mem_univ _
  rw [h] at hx
  simpa using hx

/-- Multiplicative quartic Wick amplitude on the shared connected decomposition. -/
private noncomputable def quarticWickDiagramMultiplicativeWeight (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) :
    Combinatorics.MultiplicativeWeight
      (Common.quarticDiagramConnectedDecomposition (QuarticVertexLabel Mode) N) ℂ where
  objectWeight d := quarticWickDiagramAmplitude ε β g d
  connectedWeight d := quarticWickDiagramAmplitude ε β g d.1
  weight_decompose d := by
    change quarticWickDiagramAmplitude ε β g d =
      ∏ B : d.componentPartition.parts,
        quarticWickDiagramAmplitude ε β g (d.restrictComponentConnected B.2).1
    exact quarticWickDiagramAmplitude_eq_prod_components ε β g d

/-- Fermionic Dyson Linked Cluster Theorem. -/
theorem factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_sum_connectedQuarticWickDiagramAmplitude
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (n : ℕ) (hn : n ≠ 0) :
    (n.factorial : ℂ) *
        PowerSeries.coeff n
          (dysonFormalLogPartitionFunction ε β (quarticInteraction g)) =
      ∑ d : ConnectedQuarticWickDiagram Mode n Finset.univ,
        quarticWickDiagramAmplitude ε β g d.1 := by
  have huniv : (Finset.univ : Finset (Fin n)) ≠ ∅ := fin_univ_ne_empty hn
  let W := quarticWickDiagramMultiplicativeWeight (N := n) ε β g
  have hZ :
      PowerSeries.constantCoeff
          (PowerSeries.normalizeByConstantCoeff
            (dysonPartitionSeries ε β (quarticInteraction g))) = 1 :=
    PowerSeries.constantCoeff_normalizeByConstantCoeff
      (constantCoeff_dysonPartitionSeries_ne_zero ε β (quarticInteraction g))
  have hMoment :
      Combinatorics.powerSeriesMomentSetFunction
          (α := Fin n)
          (PowerSeries.normalizeByConstantCoeff
            (dysonPartitionSeries ε β (quarticInteraction g))) hZ =
        W.normalizedObjectMoment := by
    ext T
    change (dysonVertexGeneratingFunctional ε β (quarticInteraction g)).moment T =
      ∑ d : QuarticWickDiagram Mode n T, quarticWickDiagramAmplitude ε β g d
    rw [dysonVertexGeneratingFunctional_moment]
    exact dysonVertexMoment_quarticInteraction_eq_sum_quarticWickDiagramAmplitude ε β g T
  calc
    (n.factorial : ℂ) *
        PowerSeries.coeff n
          (dysonFormalLogPartitionFunction ε β (quarticInteraction g)) =
        W.connectedContribution (Finset.univ : Finset (Fin n)) := by
      simpa [dysonFormalLogPartitionFunction] using
        (Combinatorics.factorial_mul_coeff_logOf_eq_connectedContribution
          (Z := PowerSeries.normalizeByConstantCoeff
            (dysonPartitionSeries ε β (quarticInteraction g)))
          hZ (W := W) hMoment huniv)
    _ = ∑ d : ConnectedQuarticWickDiagram Mode n Finset.univ,
          quarticWickDiagramAmplitude ε β g d.1 := by
      rfl

end Fermionic
end SecondQuantization
