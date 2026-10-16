import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.DysonSeries
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs

set_option linter.style.header false

/-!
# External-component replica projection for fixed-label Wick diagrams

For a fixed perturbative order, weight every vacuum-free Wick diagram by a
formal replica variable raised to its number of externally supported
connected components. The coefficient linear in the replica variable keeps
exactly the diagrams in which all external insertions are connected.

The weight is the existing fully signed and integrated Dyson amplitude.
This is an exact diagram-selection identity; it does *not* by itself identify
the resulting polynomial with a physical source generating functional or
prove a signed moment–cumulant factorization.
-/

namespace SecondQuantization
namespace Fermionic

open Common
open scoped BigOperators

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Order-`n` vacuum-free Wick diagrams with fixed external labels, weighted by
the number of connected components that meet the external sector. -/
noncomputable def vacuumFreeExternalInsertionReplicaPolynomial {E : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ) (n : ℕ) : Polynomial ℂ := by
  classical
  exact ∑ d : VacuumFreeFixedExternalInsertionWickDiagram Mode E n externalLabel,
    Polynomial.C (d.1.1.dysonAmplitude ε β g externalTime) *
      Polynomial.X ^ (externalComponentPartition d.1.1.vertexGraph).parts.card

open Classical in
/-- The replica-linear coefficient is precisely the sum of signed amplitudes
whose external vertices are all mutually connected. Pure vacuum components
are excluded by the input diagram family, not by replica projection. -/
theorem vacuumFreeExternalInsertionReplicaPolynomial_coeff_one
    {E : ℕ} (anchor : Fin (2 * E))
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ) (n : ℕ) :
    (vacuumFreeExternalInsertionReplicaPolynomial
      ε β g externalLabel externalTime n).coeff 1 =
      ∑ d : VacuumFreeFixedExternalInsertionWickDiagram Mode E n externalLabel,
        if AllExternalVerticesConnected d.1.1.vertexGraph then
          d.1.1.dysonAmplitude ε β g externalTime else 0 := by
  classical
  letI : Nonempty (Fin (2 * E)) := ⟨anchor⟩
  unfold vacuumFreeExternalInsertionReplicaPolynomial
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro d _
  have hcriterion :=
    allExternalVerticesConnected_iff_externalComponentPartition_parts_card_eq_one
      d.1.1.vertexGraph
  by_cases hconn : AllExternalVerticesConnected d.1.1.vertexGraph
  · have hcard := hcriterion.mp hconn
    simp [hconn, hcard]
  · have hcard : (externalComponentPartition d.1.1.vertexGraph).parts.card ≠ 1 :=
      fun hc => hconn (hcriterion.mpr hc)
    have hcard' : 1 ≠ (externalComponentPartition d.1.1.vertexGraph).parts.card :=
      Ne.symm hcard
    simp [hconn, hcard']

end Fermionic
end SecondQuantization
