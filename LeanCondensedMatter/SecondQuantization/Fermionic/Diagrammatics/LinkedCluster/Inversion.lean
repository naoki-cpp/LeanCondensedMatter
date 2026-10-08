import LeanCondensedMatter.Analysis.PowerSeries.Cumulant
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion.Moment

set_option linter.style.header false

/-!
# Fermionic Dyson linked-cluster theorem via cumulant inversion

An independent kernel-checked proof of the canonical connected-diagram result using finite-set
cumulant inversion instead of the replica method. The statistics-independent
`Combinatorics.factorial_mul_coeff_logOf_eq_connectedContribution` already expresses the
cumulant-to-connected step, so no fermionic cumulant wrapper is needed.
-/

open scoped BigOperators

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The fermionic Dyson linked-cluster theorem obtained independently through moment–cumulant
inversion. Kept as a checked example because the canonical public theorem uses replica counting. -/
example
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
  let Z :=
    PowerSeries.normalizeByConstantCoeff
      (dysonPartitionSeries ε β (quarticInteraction g))
  have hZ : PowerSeries.constantCoeff Z = 1 := by
    dsimp [Z]
    exact PowerSeries.constantCoeff_normalizeByConstantCoeff
      (constantCoeff_dysonPartitionSeries_ne_zero ε β (quarticInteraction g))
  have hMoment :
      Combinatorics.powerSeriesMomentSetFunction (α := Fin n) Z hZ =
        W.normalizedObjectMoment := by
    simpa only [Z, W] using
      (dysonPartitionSeriesMoment_eq_wickDiagramObjectMoment
        (N := n) ε β g hZ)
  calc
      Combinatorics.powerSeriesMomentSetFunction (α := Fin n) Z hZ =
          Common.dysonTraceVertexMomentSetFunction
            (fermionEnergy ε) β (quarticInteraction g) := by
        simpa only [Z, dysonPartitionSeries] using
          (Common.powerSeriesMomentSetFunction_normalizeByConstantCoeff_dysonTraceSeries_eq_dysonTraceVertexMomentSetFunction
            (α := Fin n) (fermionEnergy ε) β (quarticInteraction g) hZ)
      _ = W.normalizedObjectMoment := by
        simpa only [W, quarticWickDiagramMoment] using
          (dysonVertexMomentSetFunction_eq_quarticWickDiagramMoment
            (N := n) ε β g)
  calc
    (n.factorial : ℂ) *
        PowerSeries.coeff n
          (dysonFormalLogPartitionFunction ε β (quarticInteraction g)) =
        W.connectedContribution (Finset.univ : Finset (Fin n)) := by
      simpa [dysonFormalLogPartitionFunction, Z] using
        (Combinatorics.factorial_mul_coeff_logOf_eq_connectedContribution
          hZ W hMoment huniv)
    _ = ∑ d : ConnectedQuarticWickDiagram Mode n Finset.univ,
          quarticWickDiagramAmplitude ε β g d.1 := rfl

end Fermionic
end SecondQuantization
