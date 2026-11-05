import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ComponentSign
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.DysonSeries
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.MixedOrderData
import LeanCondensedMatter.Combinatorics.Cumulant.Moment
import Mathlib.Data.Fintype.EquivFin

set_option linter.style.header false

/-!
# Fermionic external-subset moments and connected-diagram contributions

Fix a finite, ordered family of external atomic fermion insertions.
Each even subset inherits the increasing order, field labels, and times.
Odd subsets have zero physical moments, as their pairing fibers are empty.
The empty source moment is defined to be one, independently of the interaction
order; the empty connected contribution is zero.

The weighted partition expression below is a precisely signed candidate for
the physical moment. Equality with the Dyson coefficients is a separate
combinatorial/analytic theorem: it requires the component restriction and
interaction-order shuffle to be summed over all diagram fibers. Defining a
partition sum is not a proof of that equality.
-/

namespace SecondQuantization
namespace Fermionic

open Common
open scoped BigOperators

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {E : ℕ}

/-- Canonical increasing reindexing of an even external subset, whose local
fermion field count is twice its pair count. -/
noncomputable def evenExternalSubsetOrderIso
    (S : Finset (Fin (2 * E))) (heven : Even S.card) :
    Fin (2 * (S.card / 2)) ≃o ↥S :=
  S.orderIsoOfFin (Nat.two_mul_div_two_of_even heven).symm

/-- Ordered external field labels restricted to an even subset. -/
noncomputable def evenExternalSubsetLabels
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (S : Finset (Fin (2 * E))) (heven : Even S.card) :
    Fin (2 * (S.card / 2)) → ExternalFieldLabel Mode :=
  fun i => labels (evenExternalSubsetOrderIso S heven i).1

/-- Ordered insertion times restricted to an even subset. -/
noncomputable def evenExternalSubsetTimes
    (times : Fin (2 * E) → ℝ)
    (S : Finset (Fin (2 * E))) (heven : Even S.card) :
    Fin (2 * (S.card / 2)) → ℝ :=
  fun i => times (evenExternalSubsetOrderIso S heven i).1

omit [LinearOrder Mode] [Fintype Mode] in
/-- Restricting fixed external field labels by their canonical subset order
agrees definitionally with the labels on the standalone connected component. -/
theorem evenExternalSubsetLabels_componentOrderedDiagram
    {n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (B : d.vertexGraph.componentPartition.parts) :
    evenExternalSubsetLabels d.externalLabel
      ((B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n)))).toLeft)
      (d.externalSector_card_even B) =
        (d.componentOrderedDiagram B).externalLabel := by
  rfl

omit [LinearOrder Mode] [Fintype Mode] in
/-- The same increasing external-slot reindexing transports the actual
insertion times, without sorting by the imaginary-time value. -/
theorem evenExternalSubsetTimes_component
    {n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (times : Fin (2 * E) → ℝ)
    (B : d.vertexGraph.componentPartition.parts) :
    evenExternalSubsetTimes times
      ((B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n)))).toLeft)
      (d.externalSector_card_even B) =
        d.componentExternalTime times B := by
  rfl

/-- Fully external-connected, vacuum-free Dyson coefficient using the actual
integrated signed Wick diagram amplitude, with all labels and times fixed. -/
noncomputable def connectedExternalInsertionDysonCoefficient {K : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * K) → ExternalFieldLabel Mode)
    (times : Fin (2 * K) → ℝ) (n : ℕ) : ℂ := by
  classical
  exact ∑ d : VacuumFreeFixedExternalInsertionWickDiagram Mode K n labels,
    if AllExternalVerticesConnected d.1.1.vertexGraph then
      d.1.1.dysonAmplitude ε β g times else 0

/-- The formal Dyson series of the fully external-connected diagram sector.
It is not identified with a source cumulant without the signed moment theorem. -/
noncomputable def connectedExternalInsertionDysonSeries {K : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * K) → ExternalFieldLabel Mode)
    (times : Fin (2 * K) → ℝ) : PowerSeries ℂ :=
  PowerSeries.mk (connectedExternalInsertionDysonCoefficient ε β g labels times)

/-- Physical, vacuum-normalized moment assigned to an external subset.
For odd subsets the operator expectation vanishes by fermion parity; for the
empty subset the normalized moment is one. -/
noncomputable def externalSubsetMomentSeries
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (times : Fin (2 * E) → ℝ)
    (S : Finset (Fin (2 * E))) : PowerSeries ℂ := by
  classical
  if hEmpty : S = ∅ then exact 1
  else if heven : Even S.card then
    exact vacuumFreeExternalInsertionDysonSeries ε β g
      (evenExternalSubsetLabels labels S heven)
      (evenExternalSubsetTimes times S heven)
  else exact 0

/-- A connected-diagram contribution for each external subset. Odd and empty
subsets contribute zero. This is defined from the actual integrated diagrams,
not by a formal inversion of the moment function. -/
noncomputable def externalSubsetConnectedDiagramSeries
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (times : Fin (2 * E) → ℝ)
    (S : Finset (Fin (2 * E))) : PowerSeries ℂ := by
  classical
  if hEmpty : S = ∅ then exact 0
  else if heven : Even S.card then
    exact connectedExternalInsertionDysonSeries ε β g
      (evenExternalSubsetLabels labels S heven)
      (evenExternalSubsetTimes times S heven)
  else exact 0

/-- A fixed convention for a partition's fermionic source sign. For partitions
with even blocks the choice of block order does not affect the result. Odd
blocks produce zero terms in the physical connected-diagram product. -/
noncomputable def externalPartitionSourceSign
    {S : Finset (Fin (2 * E))} (π : Finpartition S) : ℂ :=
  externalPartitionOrderSign π (Fintype.equivFin π.parts)

/-- The signed partition expansion predicted by the source/cumulant identity,
formed from the actual fully connected diagrammatic contributions.
The remaining Phase 5 theorem must identify this with
`externalSubsetMomentSeries`, coefficientwise at every Dyson order. -/
noncomputable def externalSubsetSignedConnectedMomentSeries
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (times : Fin (2 * E) → ℝ)
    (S : Finset (Fin (2 * E))) : PowerSeries ℂ :=
  Finpartition.weightedMomentFromCumulant
    (fun _ π => PowerSeries.C (externalPartitionSourceSign π))
    (externalSubsetConnectedDiagramSeries ε β g labels times) S

@[simp]
theorem externalSubsetMomentSeries_empty
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (times : Fin (2 * E) → ℝ) :
    externalSubsetMomentSeries ε β g labels times ∅ = 1 := by
  simp [externalSubsetMomentSeries]

@[simp]
theorem externalSubsetConnectedDiagramSeries_empty
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (times : Fin (2 * E) → ℝ) :
    externalSubsetConnectedDiagramSeries ε β g labels times ∅ = 0 := by
  simp [externalSubsetConnectedDiagramSeries]

/-- Odd external subsets carry neither a normalized moment nor a connected
Wick-diagram contribution. -/
theorem externalSubsetSeries_eq_zero_of_odd
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (times : Fin (2 * E) → ℝ)
    (S : Finset (Fin (2 * E))) (hodd : ¬ Even S.card) :
    externalSubsetMomentSeries ε β g labels times S = 0 ∧
      externalSubsetConnectedDiagramSeries ε β g labels times S = 0 := by
  have hne : S ≠ ∅ := by
    intro h
    subst S
    exact hodd (by simp)
  simp [externalSubsetMomentSeries, externalSubsetConnectedDiagramSeries, hne, hodd]


/-- Every partition of an odd-sized external subset contains an odd-sized block.
This makes the odd-fermion vanishing visible directly in the signed source
partition expansion, rather than only in the Wick-diagram definitions. -/
private theorem odd_externalSubset_has_odd_partition_block
    {S : Finset (Fin (2 * E))} (π : Finpartition S)
    (hodd : ¬ Even S.card) :
    ∃ B ∈ π.parts, ¬ Even B.card := by
  classical
  by_contra h
  have hall : ∀ B ∈ π.parts, Even B.card := by
    intro B hB
    by_contra hBodd
    exact h ⟨B, hB, hBodd⟩
  have hsum : ∀ T : Finset (Finset (Fin (2 * E))),
      T ⊆ π.parts → Even (∑ B ∈ T, B.card) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
        intro _
        simp
    | @insert B T hBT ih =>
        intro hsub
        rw [Finset.sum_insert hBT]
        apply Even.add
        · exact hall B (hsub (Finset.mem_insert_self B T))
        · exact ih (Finset.Subset.trans (Finset.subset_insert B T) hsub)
  have hπ := hsum π.parts (Finset.Subset.refl _)
  exact hodd (by simpa only [π.sum_card_parts] using hπ)

/-- The signed connected-partition expression respects fermion parity:
an odd number of source insertions gives zero term by term. No hypothesis
identifying the diagrammatic moments with the partition expression is used. -/
theorem externalSubsetSignedConnectedMomentSeries_eq_zero_of_odd
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (times : Fin (2 * E) → ℝ)
    (S : Finset (Fin (2 * E))) (hodd : ¬ Even S.card) :
    externalSubsetSignedConnectedMomentSeries ε β g labels times S = 0 := by
  classical
  unfold externalSubsetSignedConnectedMomentSeries Finpartition.weightedMomentFromCumulant
  apply Finset.sum_eq_zero
  intro π _
  obtain ⟨B, hB, hBodd⟩ := odd_externalSubset_has_odd_partition_block π hodd
  have hzero : externalSubsetConnectedDiagramSeries ε β g labels times B = 0 :=
    (externalSubsetSeries_eq_zero_of_odd ε β g labels times B hBodd).2
  have hprod : Finpartition.partitionProduct
      (externalSubsetConnectedDiagramSeries ε β g labels times) π = 0 := by
    unfold Finpartition.partitionProduct
    exact Finset.prod_eq_zero hB hzero
  rw [hprod, mul_zero]

end Fermionic
end SecondQuantization
