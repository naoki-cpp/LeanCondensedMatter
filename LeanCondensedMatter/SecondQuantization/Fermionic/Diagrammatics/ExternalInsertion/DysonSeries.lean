import LeanCondensedMatter.Analysis.PowerSeries.Normalization
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalComponents
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.QuarticInteraction
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.Integral
import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonPartitionSeries

set_option linter.style.header false

/-!
# Arbitrary external-insertion Dyson series

This module fixes the external fermionic field labels and packages the integrated diagram amplitudes
into perturbative coefficients and formal power series. The vacuum-free series only removes pure
vacuum connected components; distinct externally supported components remain allowed.

The coefficientwise factorization against the normalized vacuum partition series is downstream.
-/

namespace SecondQuantization
namespace Fermionic

open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Arbitrary external-insertion Wick diagrams with the external field labels fixed. -/
abbrev FixedExternalInsertionWickDiagram
    (Mode : Type*) (E n : ℕ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode) : Type _ :=
  {d : ExternalInsertionWickDiagram Mode E n // d.externalLabel = externalLabel}

/-- Fixed-external diagrams with no purely vacuum connected component.

Several disconnected components meeting the external sector remain allowed. -/
abbrev VacuumFreeFixedExternalInsertionWickDiagram
    (Mode : Type*) (E n : ℕ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode) : Type _ :=
  {d : FixedExternalInsertionWickDiagram Mode E n externalLabel //
    HasNoVacuumComponent d.1.vertexGraph}

/-- Order-`n` integrated diagram coefficient for fixed arbitrary external insertions. -/
noncomputable def externalInsertionDysonCoefficient {E : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ) (n : ℕ) : ℂ := by
  classical
  exact ∑ d : FixedExternalInsertionWickDiagram Mode E n externalLabel,
    d.1.dysonAmplitude ε β g externalTime

/-- Order-`n` coefficient after discarding diagrams with pure vacuum components. -/
noncomputable def vacuumFreeExternalInsertionDysonCoefficient {E : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ) (n : ℕ) : ℂ := by
  classical
  exact ∑ d : VacuumFreeFixedExternalInsertionWickDiagram Mode E n externalLabel,
    d.1.1.dysonAmplitude ε β g externalTime

/-- Formal Dyson series for fixed arbitrary external insertions. -/
noncomputable def externalInsertionDysonSeries {E : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ) : PowerSeries ℂ :=
  PowerSeries.mk (externalInsertionDysonCoefficient ε β g externalLabel externalTime)

/-- Formal Dyson series restricted to diagrams with no pure vacuum connected component. -/
noncomputable def vacuumFreeExternalInsertionDysonSeries {E : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ) : PowerSeries ℂ :=
  PowerSeries.mk (vacuumFreeExternalInsertionDysonCoefficient
    ε β g externalLabel externalTime)

/-- Vacuum-normalized arbitrary-external Dyson series.

The partition series is normalized to constant coefficient one because the diagram amplitudes use
free Gibbs expectations, exactly as in the two-point expansion. -/
noncomputable def vacuumNormalizedExternalInsertionDysonSeries {E : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ) : PowerSeries ℂ :=
  externalInsertionDysonSeries ε β g externalLabel externalTime *
    (PowerSeries.normalizeByConstantCoeff
      (dysonPartitionSeries ε β (quarticInteraction g)))⁻¹


/-- The vacuum-normalized arbitrary-external linked-cluster identity is equivalent to the
coefficientwise Cauchy factorization by the normalized vacuum partition coefficients.

This equivalence is formal power-series algebra. The coefficientwise hypothesis
is proved downstream using the external-support/vacuum fiber-shuffle factorization. -/
theorem vacuumNormalizedExternalInsertionDysonSeries_eq_vacuumFree_iff_cauchy
    {E : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ) :
    vacuumNormalizedExternalInsertionDysonSeries ε β g externalLabel externalTime =
        vacuumFreeExternalInsertionDysonSeries ε β g externalLabel externalTime ↔
      ∀ n : ℕ,
        externalInsertionDysonCoefficient ε β g externalLabel externalTime n =
          ∑ m ∈ Finset.range (n + 1),
            vacuumFreeExternalInsertionDysonCoefficient
                ε β g externalLabel externalTime m *
              normalizedDysonPartitionCoeff ε β (quarticInteraction g) (n - m) := by
  let vacuum : PowerSeries ℂ :=
    PowerSeries.normalizeByConstantCoeff
      (dysonPartitionSeries ε β (quarticInteraction g))
  have hvacuum : PowerSeries.constantCoeff vacuum ≠ 0 := by
    change PowerSeries.constantCoeff
      (PowerSeries.normalizeByConstantCoeff
        (dysonPartitionSeries ε β (quarticInteraction g))) ≠ 0
    rw [PowerSeries.constantCoeff_normalizeByConstantCoeff
      (constantCoeff_dysonPartitionSeries_ne_zero ε β (quarticInteraction g))]
    exact one_ne_zero
  have hcoeff :
      (externalInsertionDysonSeries ε β g externalLabel externalTime =
          vacuumFreeExternalInsertionDysonSeries ε β g externalLabel externalTime * vacuum) ↔
        ∀ n : ℕ,
          externalInsertionDysonCoefficient ε β g externalLabel externalTime n =
            ∑ m ∈ Finset.range (n + 1),
              vacuumFreeExternalInsertionDysonCoefficient
                  ε β g externalLabel externalTime m *
                normalizedDysonPartitionCoeff ε β (quarticInteraction g) (n - m) := by
    constructor
    · intro hs n
      have hn := congrArg (PowerSeries.coeff n) hs
      rw [PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hn
      simpa only [externalInsertionDysonSeries, vacuumFreeExternalInsertionDysonSeries,
        PowerSeries.coeff_mk, vacuum,
        coeff_normalizeByConstantCoeff_dysonPartitionSeries_eq_normalizedDysonPartitionCoeff]
        using hn
    · intro hs
      ext n
      rw [PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simpa only [externalInsertionDysonSeries, vacuumFreeExternalInsertionDysonSeries,
        PowerSeries.coeff_mk, vacuum,
        coeff_normalizeByConstantCoeff_dysonPartitionSeries_eq_normalizedDysonPartitionCoeff]
        using (hs n)
  constructor
  · intro h
    apply hcoeff.mp
    have hh := congrArg (fun z : PowerSeries ℂ => z * vacuum) h
    change
      (externalInsertionDysonSeries ε β g externalLabel externalTime * vacuum⁻¹) *
          vacuum =
        vacuumFreeExternalInsertionDysonSeries ε β g externalLabel externalTime * vacuum
      at hh
    rw [mul_assoc, PowerSeries.inv_mul_cancel vacuum hvacuum, mul_one] at hh
    exact hh
  · intro h
    change
      externalInsertionDysonSeries ε β g externalLabel externalTime * vacuum⁻¹ =
        vacuumFreeExternalInsertionDysonSeries ε β g externalLabel externalTime
    exact PowerSeries.mul_inv_eq_of_eq_mul_of_constantCoeff_ne_zero
      hvacuum (hcoeff.mpr h)

end Fermionic
end SecondQuantization
