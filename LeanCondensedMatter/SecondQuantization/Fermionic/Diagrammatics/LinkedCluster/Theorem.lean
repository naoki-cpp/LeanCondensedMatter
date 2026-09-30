import LeanCondensedMatter.Analysis.PowerSeries.ReplicaBridge
import LeanCondensedMatter.Analysis.PowerSeries.Moment
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

/-- Multiplicative quartic Wick amplitude on the shared connected decomposition. -/
private noncomputable def quarticWickDiagramMultiplicativeWeight (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) :
    Combinatorics.MultiplicativeWeight
      (Common.quarticDiagramConnectedDecomposition (QuarticVertexLabel Mode) N) ℂ :=
  Common.QuarticDiagram.multiplicativeWeight
    (N := N)
    (fun d => quarticWickDiagramAmplitude ε β g d)
    (fun d => quarticWickDiagramAmplitude_eq_prod_components ε β g d)

/-- Fermionic Dyson Linked Cluster Theorem. -/
theorem factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_sum_connectedQuarticWickDiagramAmplitude
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (n : ℕ) (hn : n ≠ 0) :
    (n.factorial : ℂ) *
        PowerSeries.coeff n
          (dysonFormalLogPartitionFunction ε β (quarticInteraction g)) =
      ∑ d : ConnectedQuarticWickDiagram Mode n Finset.univ,
        quarticWickDiagramAmplitude ε β g d.1 := by
  have huniv : (Finset.univ : Finset (Fin n)) ≠ ∅ :=
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩).ne_empty
  let W := quarticWickDiagramMultiplicativeWeight (N := n) ε β g
  have hZ :
      PowerSeries.constantCoeff
          (PowerSeries.normalizeByConstantCoeff
            (dysonPartitionSeries ε β (quarticInteraction g))) = 1 :=
    PowerSeries.constantCoeff_normalizeByConstantCoeff
      (constantCoeff_dysonPartitionSeries_ne_zero ε β (quarticInteraction g))
  have hSeriesMoment :
      Combinatorics.powerSeriesMomentSetFunction (α := Fin n)
          (PowerSeries.normalizeByConstantCoeff
            (dysonPartitionSeries ε β (quarticInteraction g))) hZ =
        dysonVertexMomentSetFunction ε β (quarticInteraction g) := by
    rw [Combinatorics.powerSeriesMomentSetFunction_eq_iff]
    intro T
    simp only [Combinatorics.powerSeriesMomentCoeff, dysonVertexMomentSetFunction_apply,
      dysonVertexMoment,
      coeff_normalizeByConstantCoeff_dysonPartitionSeries_eq_normalizedDysonPartitionCoeff]
  have hDiagramMoment :
      dysonVertexMomentSetFunction ε β (quarticInteraction g) =
        W.normalizedObjectMoment := by
    ext T
    exact dysonVertexMoment_quarticInteraction_eq_sum_quarticWickDiagramAmplitude ε β g T
  have hMoment :=
    (Combinatorics.powerSeriesMomentSetFunction_eq_iff
      (α := Fin n) _ hZ _).mp (hSeriesMoment.trans hDiagramMoment)
  calc
    (n.factorial : ℂ) *
        PowerSeries.coeff n
          (dysonFormalLogPartitionFunction ε β (quarticInteraction g)) =
        W.connectedContribution (Finset.univ : Finset (Fin n)) := by
      simpa [dysonFormalLogPartitionFunction] using
        (Combinatorics.factorial_mul_coeff_logOf_eq_connectedContribution_replica
          (Z := PowerSeries.normalizeByConstantCoeff
            (dysonPartitionSeries ε β (quarticInteraction g)))
          hZ (W := W) (fun T => by
            simpa only [Combinatorics.powerSeriesMomentCoeff,
              Combinatorics.MultiplicativeWeight.normalizedObjectMoment_apply] using hMoment T)
          huniv)
    _ = ∑ d : ConnectedQuarticWickDiagram Mode n Finset.univ,
          quarticWickDiagramAmplitude ε β g d.1 := by
      rfl

end Fermionic
end SecondQuantization
