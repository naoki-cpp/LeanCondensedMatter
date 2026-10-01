import LeanCondensedMatter.Analysis.PowerSeries.Cumulant
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion.Moment
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.Wick.Cumulant

set_option linter.style.header false

/-!
# Fermionic Dyson linked-cluster theorem via cumulant inversion

Provides an independent Möbius-inversion proof of the finite-mode fermionic Dyson linked-cluster
identity. The canonical theorem remains replica-based; this theorem factors through the bundled
Dyson moment, Wick-diagram moment, and Wick-diagram cumulant APIs.
-/

open scoped BigOperators

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Fermionic Dyson Linked Cluster Theorem proved through finite-set cumulant inversion rather than
the replica bridge. -/
theorem factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_sum_connectedQuarticWickDiagramAmplitude_inversion
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (n : ℕ) (hn : n ≠ 0) :
    (n.factorial : ℂ) *
        PowerSeries.coeff n
          (dysonFormalLogPartitionFunction ε β (quarticInteraction g)) =
      ∑ d : ConnectedQuarticWickDiagram Mode n Finset.univ,
        quarticWickDiagramAmplitude ε β g d.1 := by
  have huniv : (Finset.univ : Finset (Fin n)) ≠ ∅ :=
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩).ne_empty
  let Z :=
    PowerSeries.normalizeByConstantCoeff
      (dysonPartitionSeries ε β (quarticInteraction g))
  have hZ : PowerSeries.constantCoeff Z = 1 := by
    dsimp [Z]
    exact PowerSeries.constantCoeff_normalizeByConstantCoeff
      (constantCoeff_dysonPartitionSeries_ne_zero ε β (quarticInteraction g))
  have hSeriesMoment :
      powerSeriesMomentSetFunction (α := Fin n) Z hZ =
        dysonVertexMomentSetFunction ε β (quarticInteraction g) := by
    simpa only [Z] using
      (powerSeriesMomentSetFunction_normalizedDysonPartitionSeries_eq_dysonVertexMomentSetFunction
        (α := Fin n) ε β (quarticInteraction g) hZ)
  have hDiagramMoment :
      dysonVertexMomentSetFunction ε β (quarticInteraction g) =
        quarticWickDiagramMoment (N := n) ε β g :=
    dysonVertexMomentSetFunction_eq_quarticWickDiagramMoment
      (N := n) ε β g
  calc
    (n.factorial : ℂ) *
        PowerSeries.coeff n
          (dysonFormalLogPartitionFunction ε β (quarticInteraction g)) =
        (powerSeriesMomentSetFunction (α := Fin n) Z hZ).cumulant
          (Finset.univ : Finset (Fin n)) := by
      change
        (n.factorial : ℂ) * PowerSeries.coeff n (PowerSeries.logOf Z) =
          Finpartition.cumulantFromMoment
            (fun T : Finset (Fin n) => powerSeriesMomentCoeff Z T.card)
            (Finset.univ : Finset (Fin n))
      exact factorial_mul_coeff_logOf_eq_cumulantFromMoment hZ huniv
    _ = (dysonVertexMomentSetFunction ε β (quarticInteraction g)).cumulant
          (Finset.univ : Finset (Fin n)) := by
      rw [hSeriesMoment]
    _ = quarticWickDiagramCumulant (N := n) ε β g
          (Finset.univ : Finset (Fin n)) := by
      rw [hDiagramMoment]
      rfl
    _ = ∑ d : ConnectedQuarticWickDiagram Mode n Finset.univ,
          quarticWickDiagramAmplitude ε β g d.1 :=
      quarticWickDiagramCumulant_eq_sum_connectedQuarticWickDiagramAmplitude
        ε β g huniv

end Fermionic
end SecondQuantization
