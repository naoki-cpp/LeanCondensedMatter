import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.SlotSplit.ExternalSupportFiberSum
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.DysonSeries
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

set_option linter.style.header false

/-!
# Fixed-external Dyson coefficients over support fibers

The generic external-support fiber sum applies to arbitrary external field labels. For a
fixed-external Dyson coefficient, the label constraint is retained on the vacuum-free
external-bearing factor: the vacuum complement carries no external labels.

This is a finite reindexing of the integrated diagram amplitudes, not yet an analytic
factorization of the ordered-simplex integrals.
-/

namespace SecondQuantization
namespace Fermionic

open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

open Classical in
/-- Reindex the integrated arbitrary-external Dyson coefficient by the externally supported
interaction slots and the vacuum-free external / quartic diagram pair. Only the external
factor carries the fixed-label constraint. -/
theorem externalInsertionDysonCoefficient_eq_sum_externalSupportFiber
    {E : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ) (n : ℕ) :
    externalInsertionDysonCoefficient ε β g externalLabel externalTime n =
      ∑ T : {T : Finset (Fin n) // T ⊆ Finset.univ},
        ∑ p : {ext : ExternalInsertionDiagram
              (ExternalFieldLabel Mode) (QuarticVertexLabel Mode) E n T.1 //
              HasNoVacuumComponent ext.vertexGraph} ×
              QuarticDiagram (QuarticVertexLabel Mode) n
                ((Finset.univ : Finset (Fin n)) \ T.1),
          if p.1.1.externalLabel = externalLabel then
            ExternalInsertionWickDiagram.dysonAmplitude
              (((ExternalInsertionDiagram.externalSupportFiberEquiv T.2).symm p).1 :
                ExternalInsertionWickDiagram Mode E n)
              ε β g externalTime
          else 0 := by
  classical
  have hfixed :
      (∑ d : FixedExternalInsertionWickDiagram Mode E n externalLabel,
        d.1.dysonAmplitude ε β g externalTime) =
        ∑ d : ExternalInsertionWickDiagram Mode E n,
          if d.externalLabel = externalLabel then
            d.dysonAmplitude ε β g externalTime
          else 0 := by
    calc
      _ = ∑ d ∈ (Finset.univ : Finset (ExternalInsertionWickDiagram Mode E n)).filter
            (fun d => d.externalLabel = externalLabel),
            d.dysonAmplitude ε β g externalTime := by
          rw [Finset.sum_subtype
            (p := fun d : ExternalInsertionWickDiagram Mode E n =>
              d.externalLabel = externalLabel)
            _ (fun d => by simp)
            (fun d => d.dysonAmplitude ε β g externalTime)]
      _ = _ := by
        simp only [Finset.sum_filter]
  unfold externalInsertionDysonCoefficient
  rw [hfixed]
  rw [ExternalInsertionDiagram.sum_eq_sum_externalSupportFiber]
  apply Finset.sum_congr rfl
  intro T _
  apply Finset.sum_congr rfl
  intro p _
  have hlabel :
      ((ExternalInsertionDiagram.externalSupportFiberEquiv T.2).symm p).1.externalLabel =
        p.1.1.externalLabel := rfl
  rw [hlabel]

open Classical in
/-- Group the external-support fibers by their number of interaction vertices.

This is the fixed-external coefficient in the cardinality coordinates needed for the binary
external/vacuum slot-shuffle decomposition. No amplitude product is asserted here. -/
theorem externalInsertionDysonCoefficient_eq_sum_powersetCard_externalSupportFiber
    {E : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ) (n : ℕ) :
    externalInsertionDysonCoefficient ε β g externalLabel externalTime n =
      ∑ m ∈ Finset.range (n + 1),
        ∑ T ∈ Finset.powersetCard m (Finset.univ : Finset (Fin n)),
          ∑ p : {ext : ExternalInsertionDiagram
                (ExternalFieldLabel Mode) (QuarticVertexLabel Mode) E n T //
                HasNoVacuumComponent ext.vertexGraph} ×
                QuarticDiagram (QuarticVertexLabel Mode) n
                  ((Finset.univ : Finset (Fin n)) \ T),
            if p.1.1.externalLabel = externalLabel then
              ExternalInsertionWickDiagram.dysonAmplitude
                (((ExternalInsertionDiagram.externalSupportFiberEquiv
                    (Finset.subset_univ T)).symm p).1 :
                    ExternalInsertionWickDiagram Mode E n)
                ε β g externalTime
            else 0 := by
  classical
  rw [externalInsertionDysonCoefficient_eq_sum_externalSupportFiber]
  let F : Finset (Fin n) → ℂ := fun T =>
    ∑ p : {ext : ExternalInsertionDiagram
          (ExternalFieldLabel Mode) (QuarticVertexLabel Mode) E n T //
          HasNoVacuumComponent ext.vertexGraph} ×
          QuarticDiagram (QuarticVertexLabel Mode) n
            ((Finset.univ : Finset (Fin n)) \ T),
      if p.1.1.externalLabel = externalLabel then
        ExternalInsertionWickDiagram.dysonAmplitude
          (((ExternalInsertionDiagram.externalSupportFiberEquiv
              (Finset.subset_univ T)).symm p).1 :
              ExternalInsertionWickDiagram Mode E n)
          ε β g externalTime
      else 0
  change
    (∑ T : {T : Finset (Fin n) // T ⊆ Finset.univ}, F T.1) =
      ∑ m ∈ Finset.range (n + 1),
        ∑ T ∈ Finset.powersetCard m (Finset.univ : Finset (Fin n)), F T
  rw [← Finset.sum_subtype
    (p := fun T : Finset (Fin n) => T ⊆ Finset.univ)
    ((Finset.univ : Finset (Fin n)).powerset)
    (fun T => by simp)
    F]
  rw [Finset.sum_powerset]
  simp only [Finset.card_univ, Fintype.card_fin]

end Fermionic
end SecondQuantization
