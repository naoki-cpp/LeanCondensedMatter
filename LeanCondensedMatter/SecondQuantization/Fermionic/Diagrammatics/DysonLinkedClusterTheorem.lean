import LeanCondensedMatter.Combinatorics.PowerSeriesCumulant
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonConnectedDiagramExpansion

set_option linter.style.header false

/-!
# Fermionic Dyson linked cluster theorem

This file completes the algebraic finite-mode fermionic Linked Cluster Theorem. It specializes the
formal-power-series / finite-set-cumulant bridge to the normalized Dyson partition series, identifies
the resulting finite-set cumulant with `dysonVertexCumulant`, and then applies the connected quartic
Wick-diagram formula.

The result is purely formal and algebraic. It makes no convergence claim and does not identify the
Dyson power series with an analytic interacting partition function.
-/

open scoped BigOperators

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

omit [LinearOrder Mode] in
/-- The coefficients of the normalized Dyson partition series are the normalized Dyson partition
coefficients. -/
theorem coeff_normalizePartitionSeries_dysonPartitionSeries_eq_normalizedDysonPartitionCoeff
    (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (n : ℕ) :
    PowerSeries.coeff n (normalizePartitionSeries (dysonPartitionSeries ε β V)) =
      normalizedDysonPartitionCoeff ε β V n := by
  simp [normalizePartitionSeries, constantCoeff_dysonPartitionSeries,
    coeff_dysonPartitionSeries, normalizedDysonPartitionCoeff,
    div_eq_mul_inv, mul_comm]

omit [LinearOrder Mode] in
/-- The factorial-normalized coefficient of the formal logarithm of the normalized Dyson partition
series is its finite-set Dyson vertex cumulant. -/
theorem factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_dysonVertexCumulant
    (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode)
    (n : ℕ) (hn : n ≠ 0) :
    (n.factorial : ℂ) *
        PowerSeries.coeff n (dysonFormalLogPartitionFunction ε β V) =
      dysonVertexCumulant ε β V (Finset.univ : Finset (Fin n)) := by
  unfold dysonVertexCumulant
  change (n.factorial : ℂ) *
      PowerSeries.coeff n
        (PowerSeries.logOf (normalizePartitionSeries (dysonPartitionSeries ε β V))) =
    Finpartition.cumulantFromMoment (dysonVertexMoment ε β V)
      (Finset.univ : Finset (Fin n))
  calc
    (n.factorial : ℂ) *
        PowerSeries.coeff n
          (PowerSeries.logOf (normalizePartitionSeries (dysonPartitionSeries ε β V))) =
      Finpartition.cumulantFromMoment
        (fun S : Finset (Fin n) =>
          (S.card.factorial : ℂ) *
            PowerSeries.coeff S.card
              (normalizePartitionSeries (dysonPartitionSeries ε β V)))
        Finset.univ :=
      Combinatorics.factorial_mul_coeff_logOf_eq_cumulantFromMoment_fin
        (constantCoeff_normalizePartitionSeries_dysonPartitionSeries ε β V) n hn
    _ = Finpartition.cumulantFromMoment (dysonVertexMoment ε β V)
        (Finset.univ : Finset (Fin n)) := by
      congr 1
      funext S
      rw [dysonVertexMoment,
        coeff_normalizePartitionSeries_dysonPartitionSeries_eq_normalizedDysonPartitionCoeff]

/-- **Fermionic Dyson Linked Cluster Theorem.** For every nonzero perturbation order, the
factorial-normalized coefficient of the formal logarithm of the normalized quartic Dyson partition
series is the sum of amplitudes of connected quartic Wick diagrams on the labelled vertex set
`Finset.univ : Finset (Fin n)`.

This is an algebraic identity of formal power-series coefficients. It assumes neither convergence nor
equality with an analytic interacting partition function. -/
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

end SecondQuantization
