import LeanCondensedMatter.Analysis.PowerSeries.Cumulant
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.LinkedCluster.ConnectedDiagramExpansion

set_option linter.style.header false

/-!
# Fermionic Dyson linked cluster theorem

This file specializes the formal-power-series / finite-set-cumulant bridge to the canonically
normalized Dyson partition series and identifies the result with connected quartic Wick diagrams.
-/

open scoped BigOperators

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

omit [LinearOrder Mode] in
/-- The factorial-normalized coefficient of the formal logarithm of the normalized Dyson partition
series is its finite-set Dyson vertex cumulant. -/
theorem factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_dysonVertexCumulant
    (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode)
    (n : ℕ) (hn : n ≠ 0) :
    (n.factorial : ℂ) *
        PowerSeries.coeff n (dysonFormalLogPartitionFunction ε β V) =
      dysonVertexCumulant ε β V (Finset.univ : Finset (Fin n)) := by
  unfold dysonVertexCumulant
  change (n.factorial : ℂ) *
      PowerSeries.coeff n
        (PowerSeries.logOf
          (PowerSeries.normalizeByConstantCoeff (dysonPartitionSeries ε β V))) =
    Finpartition.cumulantFromMoment (dysonVertexMoment ε β V)
      (Finset.univ : Finset (Fin n))
  calc
    (n.factorial : ℂ) *
        PowerSeries.coeff n
          (PowerSeries.logOf
            (PowerSeries.normalizeByConstantCoeff (dysonPartitionSeries ε β V))) =
      Finpartition.cumulantFromMoment
        (fun S : Finset (Fin n) =>
          (S.card.factorial : ℂ) *
            PowerSeries.coeff S.card
              (PowerSeries.normalizeByConstantCoeff (dysonPartitionSeries ε β V)))
        Finset.univ :=
      Combinatorics.factorial_mul_coeff_logOf_eq_cumulantFromMoment_fin
        (constantCoeff_normalizeByConstantCoeff_dysonPartitionSeries ε β V) n hn
    _ = Finpartition.cumulantFromMoment (dysonVertexMoment ε β V)
        (Finset.univ : Finset (Fin n)) := by
      congr 1
      funext S
      rw [dysonVertexMoment,
        coeff_normalizeByConstantCoeff_dysonPartitionSeries_eq_normalizedDysonPartitionCoeff]

/-- Fermionic Dyson Linked Cluster Theorem. -/
theorem factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_sum_connectedAmplitude
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (n : ℕ) (hn : n ≠ 0) :
    (n.factorial : ℂ) *
        PowerSeries.coeff n
          (dysonFormalLogPartitionFunction ε β (quarticInteraction g)) =
      ∑ d : ConnectedQuarticWickDiagram Mode n Finset.univ,
        quarticWickDiagramAmplitude ε β g d.1 := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have huniv : (Finset.univ : Finset (Fin n)) ≠ ∅ := by
    intro h
    have hx : (⟨0, hnpos⟩ : Fin n) ∈ (Finset.univ : Finset (Fin n)) :=
      Finset.mem_univ _
    rw [h] at hx
    simpa using hx
  calc
    (n.factorial : ℂ) *
        PowerSeries.coeff n
          (dysonFormalLogPartitionFunction ε β (quarticInteraction g)) =
        dysonVertexCumulant ε β (quarticInteraction g)
          (Finset.univ : Finset (Fin n)) :=
      factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_dysonVertexCumulant
        ε β (quarticInteraction g) n hn
    _ = ∑ d : ConnectedQuarticWickDiagram Mode n Finset.univ,
          quarticWickDiagramAmplitude ε β g d.1 :=
      dysonVertexCumulant_quarticInteraction_eq_sum_connectedQuarticWickDiagramAmplitude
        ε β g huniv

end Fermionic
end SecondQuantization
