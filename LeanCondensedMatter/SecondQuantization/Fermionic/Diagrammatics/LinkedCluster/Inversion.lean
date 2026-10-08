import LeanCondensedMatter.Analysis.PowerSeries.Cumulant
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion.Moment
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.Wick.Cumulant

set_option linter.style.header false

/-!
# Fermionic Dyson linked-cluster theorem via cumulant inversion

Provides the Möbius-inversion route from the fermionic Dyson formal logarithm to the bundled Wick
diagram cumulant. The canonical connected-diagram theorem remains replica-based; this module also
kernel-checks the full inversion route to the same connected-diagram sum as an `example`.
-/

open scoped BigOperators

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The factorial-normalized fermionic Dyson formal-log coefficient is the corresponding Wick
diagram cumulant, proved through finite-set cumulant inversion rather than the replica bridge. -/
theorem factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_quarticWickDiagramCumulant
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (n : ℕ) (hn : n ≠ 0) :
    (n.factorial : ℂ) *
        PowerSeries.coeff n
          (dysonFormalLogPartitionFunction ε β (quarticInteraction g)) =
      quarticWickDiagramCumulant (N := n) ε β g
        (Finset.univ : Finset (Fin n)) := by
  have huniv : (Finset.univ : Finset (Fin n)) ≠ ∅ :=
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩).ne_empty
  let Z :=
    PowerSeries.normalizeByConstantCoeff
      (dysonPartitionSeries ε β (quarticInteraction g))
  have hZ : PowerSeries.constantCoeff Z = 1 := by
    dsimp [Z]
    exact PowerSeries.constantCoeff_normalizeByConstantCoeff
      (constantCoeff_dysonPartitionSeries_ne_zero ε β (quarticInteraction g))
  have hMoment :
      powerSeriesMomentSetFunction (α := Fin n) Z hZ =
        quarticWickDiagramMoment (N := n) ε β g := by
    calc
      powerSeriesMomentSetFunction (α := Fin n) Z hZ =
          Common.dysonTraceVertexMomentSetFunction (fermionEnergy ε) β (quarticInteraction g) := by
        simpa only [Z, dysonPartitionSeries] using
          (Common.powerSeriesMomentSetFunction_normalizeByConstantCoeff_dysonTraceSeries_eq_dysonTraceVertexMomentSetFunction (α := Fin n) (fermionEnergy ε) β (quarticInteraction g) hZ)
      _ = quarticWickDiagramMoment (N := n) ε β g :=
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
      simpa only [powerSeriesMomentCoeff, Finset.card_univ, Fintype.card_fin] using
        (factorial_mul_coeff_logOf_eq_cumulantFromMoment
          (α := Fin n) (s := (Finset.univ : Finset (Fin n))) hZ huniv)
    _ = quarticWickDiagramCumulant (N := n) ε β g
          (Finset.univ : Finset (Fin n)) := by
      rw [hMoment]
      rfl

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
  calc
    (n.factorial : ℂ) *
        PowerSeries.coeff n
          (dysonFormalLogPartitionFunction ε β (quarticInteraction g)) =
        quarticWickDiagramCumulant (N := n) ε β g
          (Finset.univ : Finset (Fin n)) :=
      factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_quarticWickDiagramCumulant
        ε β g n hn
    _ = ∑ d : ConnectedQuarticWickDiagram Mode n Finset.univ,
          quarticWickDiagramAmplitude ε β g d.1 :=
      quarticWickDiagramCumulant_eq_sum_connectedQuarticWickDiagramAmplitude
        ε β g huniv

end Fermionic
end SecondQuantization
