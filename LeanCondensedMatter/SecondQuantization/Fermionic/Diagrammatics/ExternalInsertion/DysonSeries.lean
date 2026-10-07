import LeanCondensedMatter.Analysis.PowerSeries.Normalization
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalComponents
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.QuarticInteraction
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ComponentIntegral
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

end Fermionic
end SecondQuantization
