import LeanCondensedMatter.Analysis.PowerSeries.ReplicaBridge
import LeanCondensedMatter.Analysis.PowerSeries.Moment
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion

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

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

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
        dysonVertexMomentSetFunction ε β (quarticInteraction g) :=
    powerSeriesMomentSetFunction_normalizedDysonPartitionSeries_eq_dysonVertexMomentSetFunction
      ε β (quarticInteraction g) hZ
  have hDiagramMoment :
      dysonVertexMomentSetFunction ε β (quarticInteraction g) =
        W.normalizedObjectMoment := by
    simpa only [W, quarticWickDiagramMoment] using
      (dysonVertexMomentSetFunction_eq_quarticWickDiagramMoment
        (N := n) ε β g)
  calc
    (n.factorial : ℂ) *
        PowerSeries.coeff n
          (dysonFormalLogPartitionFunction ε β (quarticInteraction g)) =
        W.connectedContribution (Finset.univ : Finset (Fin n)) := by
      simpa [dysonFormalLogPartitionFunction] using
        (Combinatorics.factorial_mul_coeff_logOf_eq_connectedContribution_replica
          (Z := PowerSeries.normalizeByConstantCoeff
            (dysonPartitionSeries ε β (quarticInteraction g)))
          hZ (W := W) (hSeriesMoment.trans hDiagramMoment) huniv)
    _ = ∑ d : ConnectedQuarticWickDiagram Mode n Finset.univ,
          quarticWickDiagramAmplitude ε β g d.1 := by
      rfl

end Fermionic
end SecondQuantization
