import LeanCondensedMatter.Analysis.PowerSeries
import LeanCondensedMatter.Combinatorics.Cumulant.ConnectedDecompositionInversion
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Components.ComponentDecompositionEquiv
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.GeneratingFunctional
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.Wick.AmplitudeFactorization
import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonVertexMoment

set_option linter.style.header false

/-!
# Fermionic Dyson linked cluster theorem

The normalized Dyson source functional is identified directly with the connected quartic Wick
amplitude sum, and the generic formal-log/source-cumulant bridge then yields the canonical formal
Linked Cluster Theorem.
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

private theorem dysonVertexGeneratingFunctional_connected_quarticInteraction_eq_sum_connected
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {S : Finset (Fin N)} (hS : S ≠ ∅) :
    (dysonVertexGeneratingFunctional ε β (quarticInteraction g)).connected S =
      ∑ d : ConnectedQuarticWickDiagram Mode N S,
        quarticWickDiagramAmplitude ε β g d.1 := by
  let W := quarticWickDiagramMultiplicativeWeight (N := N) ε β g
  calc
    (dysonVertexGeneratingFunctional ε β (quarticInteraction g)).connected S =
        Finpartition.cumulantFromMoment W.objectMoment S := by
      change Finpartition.cumulantFromMoment
          (dysonVertexGeneratingFunctional ε β (quarticInteraction g)).moment S =
        Finpartition.cumulantFromMoment W.objectMoment S
      congr 1
      funext T
      rw [dysonVertexGeneratingFunctional_moment]
      change dysonVertexMoment ε β (quarticInteraction g) T =
        ∑ d : QuarticWickDiagram Mode N T, quarticWickDiagramAmplitude ε β g d
      exact dysonVertexMoment_quarticInteraction_eq_sum_quarticWickDiagramAmplitude ε β g T
    _ = W.connectedContribution S := W.cumulantFromMoment_objectMoment hS
    _ = ∑ d : ConnectedQuarticWickDiagram Mode N S,
        quarticWickDiagramAmplitude ε β g d.1 := by
      rfl

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
  calc
    (n.factorial : ℂ) *
        PowerSeries.coeff n
          (dysonFormalLogPartitionFunction ε β (quarticInteraction g)) =
        (dysonVertexGeneratingFunctional ε β (quarticInteraction g)).connected
          (Finset.univ : Finset (Fin n)) := by
      simpa [dysonFormalLogPartitionFunction, dysonVertexGeneratingFunctional] using
        (Common.factorial_mul_coeff_logOf_normalizeByConstantCoeff_eq_connected
          (Z := dysonPartitionSeries ε β (quarticInteraction g)) (Source := Fin n)
          (constantCoeff_dysonPartitionSeries_ne_zero ε β (quarticInteraction g)) huniv)
    _ = ∑ d : ConnectedQuarticWickDiagram Mode n Finset.univ,
          quarticWickDiagramAmplitude ε β g d.1 :=
      dysonVertexGeneratingFunctional_connected_quarticInteraction_eq_sum_connected
        ε β g huniv

end Fermionic
end SecondQuantization
