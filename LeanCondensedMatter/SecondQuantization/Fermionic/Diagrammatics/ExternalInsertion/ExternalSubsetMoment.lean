import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ExternalSourceCumulant
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.InteractionPictureVertexDyson
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ExternalVacuumFiberCauchySum
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.MixedOrderData
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.ExternalPartition
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.BlockAssembly
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
/-- Independently assembled Wick blocks have exactly the physically
restricted external-source labels in canonical increasing order. This
identifies the source-label part of the future actual-component/local-block
comparison without imposing or changing any source sign. -/
theorem ExternalInsertionBlockLayout.assembleDiagram_externalLabel_eq_evenExternalSubsetLabels
    {n : ℕ} (layout : ExternalInsertionBlockLayout E n)
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram (ExternalFieldLabel Mode) (QuarticVertexLabel Mode)
        ((B : Finset (Fin (2 * E))).card / 2) n
        (layout.interactionBlock (Finset.univ : Finset (Fin n)) B))
    (B : layout.partition.parts) :
    (F B).externalLabel =
      evenExternalSubsetLabels
        (layout.assembleDiagram (Finset.univ : Finset (Fin n)) F).externalLabel
        (B : Finset (Fin (2 * E))) (layout.evenBlocks B) := by
  classical
  funext i
  simpa only [evenExternalSubsetLabels, evenExternalSubsetOrderIso,
    layout.sourceEquiv_symm_apply] using
    (layout.assembleDiagram_externalLabel
      (Finset.univ : Finset (Fin n)) F B i).symm

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


/-- Restricting an external-field family to an even subset is invariant,
up to dependent equality, under equality of the actual source slot sets.
The two parity witnesses need not be definitionally the same. -/
private theorem evenExternalSubsetRestriction_heq_of_eq
    {Value : Type*} (F : Fin (2 * E) → Value)
    {S T : Finset (Fin (2 * E))}
    (hs : Even S.card) (ht : Even T.card) (hST : S = T) :
    HEq
      (fun i => F (evenExternalSubsetOrderIso S hs i).1)
      (fun i => F (evenExternalSubsetOrderIso T ht i).1) := by
  cases hST
  rfl

omit [LinearOrder Mode] [Fintype Mode] in
/-- In a physical assembly of independently connected Wick blocks, the
canonical standalone physical connected component has the same external
source labels as the originally supplied local diagram, up to the
dependent equality of its physically reconstructed external-pair count. -/
theorem ExternalInsertionBlockLayout.assembleDiagram_componentOrderedDiagram_externalLabel
    {n : ℕ} (layout : ExternalInsertionBlockLayout E n)
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram (ExternalFieldLabel Mode) (QuarticVertexLabel Mode)
        ((B : Finset (Fin (2 * E))).card / 2) n
        (layout.interactionBlock (Finset.univ : Finset (Fin n)) B))
    (hconnected : ∀ B, (F B).vertexGraph.Preconnected)
    (e : Fin (2 * E)) :
    HEq (F (layout.sourceEquiv e).1).externalLabel
      ((layout.assembleDiagram (Finset.univ : Finset (Fin n)) F).componentOrderedDiagram
        ⟨(layout.assembleDiagram (Finset.univ : Finset (Fin n)) F).vertexGraph.componentBlock
            (Sum.inl e),
          (layout.assembleDiagram (Finset.univ : Finset (Fin n)) F).vertexGraph.componentBlock_mem_componentPartition
            (Sum.inl e)⟩).externalLabel := by
  classical
  let d := layout.assembleDiagram (Finset.univ : Finset (Fin n)) F
  let B := (layout.sourceEquiv e).1
  let C : d.vertexGraph.componentPartition.parts :=
    ⟨d.vertexGraph.componentBlock (Sum.inl e),
      d.vertexGraph.componentBlock_mem_componentPartition (Sum.inl e)⟩
  have hsec : (B : Finset (Fin (2 * E))) =
      (C.1 : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n)))).toLeft :=
    (layout.assembleDiagram_componentExternalSector_external
      (Finset.univ : Finset (Fin n)) F hconnected e).symm
  have hlabels :
      (F B).externalLabel =
        evenExternalSubsetLabels d.externalLabel (B : Finset (Fin (2 * E)))
          (layout.evenBlocks B) :=
    ExternalInsertionBlockLayout.assembleDiagram_externalLabel_eq_evenExternalSubsetLabels layout F B
  have htransport :=
    evenExternalSubsetRestriction_heq_of_eq d.externalLabel
      (layout.evenBlocks B) (d.externalSector_card_even C) hsec
  have hcomponent := evenExternalSubsetLabels_componentOrderedDiagram (d := d) C
  exact (heq_of_eq hlabels).trans (htransport.trans (heq_of_eq hcomponent))

omit [LinearOrder Mode] [Fintype Mode] in
/-- On each external-partition block of a vacuum-free diagram, the field
labels used by the source-subset moment are exactly the labels of the
canonical standalone connected-component diagram.

The inverse component/block equivalence is essential here: the statement
does not select an arbitrary representative of a block. -/
theorem evenExternalSubsetLabels_externalPartitionBlock
    {n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (hVac : HasNoVacuumComponent d.vertexGraph)
    (P : (externalComponentPartition d.vertexGraph).parts) :
    HEq
      (evenExternalSubsetLabels d.externalLabel
        (P : Finset (Fin (2 * E)))
        (d.externalComponentPartition_block_card_even P.1 P.2))
      ((d.componentOrderedDiagram
        ((d.vacuumFreeComponentsEquivExternalBlocks hVac).symm P)).externalLabel) := by
  let B := (d.vacuumFreeComponentsEquivExternalBlocks hVac).symm P
  exact (evenExternalSubsetRestriction_heq_of_eq d.externalLabel
    (d.externalComponentPartition_block_card_even P.1 P.2)
    (d.externalSector_card_even B)
    (d.vacuumFreeComponentsEquivExternalBlocks_symm_apply hVac P).symm).trans
      (heq_of_eq (evenExternalSubsetLabels_componentOrderedDiagram (d := d) B))

omit [LinearOrder Mode] [Fintype Mode] in
/-- The same external-block transport preserves the insertion times in
increasing source-slot order, not in the order of their numerical values. -/
theorem evenExternalSubsetTimes_externalPartitionBlock
    {n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (hVac : HasNoVacuumComponent d.vertexGraph)
    (times : Fin (2 * E) → ℝ)
    (P : (externalComponentPartition d.vertexGraph).parts) :
    HEq
      (evenExternalSubsetTimes times
        (P : Finset (Fin (2 * E)))
        (d.externalComponentPartition_block_card_even P.1 P.2))
      (d.componentExternalTime times
        ((d.vacuumFreeComponentsEquivExternalBlocks hVac).symm P)) := by
  let B := (d.vacuumFreeComponentsEquivExternalBlocks hVac).symm P
  exact (evenExternalSubsetRestriction_heq_of_eq times
    (d.externalComponentPartition_block_card_even P.1 P.2)
    (d.externalSector_card_even B)
    (d.vacuumFreeComponentsEquivExternalBlocks_symm_apply hVac P).symm).trans
      (heq_of_eq (evenExternalSubsetTimes_component (d := d) times B))

omit [LinearOrder Mode] in
/-- Explicit finite enumeration of vacuum-free fixed-label diagrams, available
when the target type is mentioned in a theorem statement rather than inside
a `by classical` proof. -/
private noncomputable instance vacuumFreeFixedExternalInsertionWickDiagramFintype
    {K n : ℕ} (labels : Fin (2 * K) → ExternalFieldLabel Mode) :
    Fintype (VacuumFreeFixedExternalInsertionWickDiagram Mode K n labels) := by
  classical
  exact Fintype.ofFinite _

/-- Reindex the actual vacuum-free fixed-label Dyson-diagram coefficient by its
induced external-component partition. The indicator selects precisely the
fiber over each partition; retaining the ambient finite type avoids creating
additional dependent-fiber `Fintype` instances in a theorem statement.

This is a finite reindexing, not yet the connected-component amplitude
factorization or the physical signed partition identity. -/
theorem vacuumFreeExternalInsertionDysonCoefficient_eq_sum_externalPartitionFibers
    {K : ℕ} (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * K) → ExternalFieldLabel Mode)
    (times : Fin (2 * K) → ℝ) (n : ℕ) :
    vacuumFreeExternalInsertionDysonCoefficient ε β g labels times n =
      ∑ π : Finpartition (Finset.univ : Finset (Fin (2 * K))),
        ∑ d : VacuumFreeFixedExternalInsertionWickDiagram Mode K n labels,
          if externalComponentPartition d.1.1.vertexGraph = π then
            d.1.1.dysonAmplitude ε β g times else 0 := by
  classical
  unfold vacuumFreeExternalInsertionDysonCoefficient
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  apply Finset.sum_congr
  · ext d
    simp
  · intro d _
    rfl

open Classical in
/-- At each fixed perturbation order, the *integrated fermionic Dyson
amplitude* sum over diagrams respecting a prescribed even external-block
layout and a fixed family of external field labels is exactly the sum over
independent block-local labelled Wick diagrams. This is an exact
finite-dimensional sum reindexing, prior to evaluating the interaction-time
shuffles or reorganizing the connected partition fibers. -/
theorem externalInsertionDysonAmplitude_sum_blockRespectingFixedLabels
    {K n : ℕ} (layout : ExternalInsertionBlockLayout K n)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * K) → ExternalFieldLabel Mode)
    (times : Fin (2 * K) → ℝ) :
    (∑ d : {d : ExternalInsertionWickDiagram Mode K n //
        (∀ leg,
          (layout.legEquiv (Finset.univ : Finset (Fin n))
            (d.pairing.partner leg)).1 =
          (layout.legEquiv (Finset.univ : Finset (Fin n)) leg).1) ∧
          d.externalLabel = labels},
        d.1.dysonAmplitude ε β g times) =
      ∑ F : {F : ∀ B : layout.partition.parts,
          ExternalInsertionDiagram (ExternalFieldLabel Mode)
            (QuarticVertexLabel Mode)
            ((B : Finset (Fin (2 * K))).card / 2) n
            (layout.interactionBlock (Finset.univ : Finset (Fin n)) B) //
          ∀ B, (F B).externalLabel =
            fun i => labels (layout.sourceEquiv.symm ⟨B, i⟩)},
        ExternalInsertionWickDiagram.dysonAmplitude
          (layout.assembleDiagram (Finset.univ : Finset (Fin n)) F.1)
          ε β g times := by
  simpa only [layout.assemblyEquivBlockRespectingFixedLabels_apply] using
    (Equiv.sum_comp
      (layout.assemblyEquivBlockRespectingFixedLabels
        (InternalLabel := QuarticVertexLabel Mode)
        (Finset.univ : Finset (Fin n)) labels)
      (fun d => ExternalInsertionWickDiagram.dysonAmplitude d.1 ε β g times)).symm

open Classical in
/-- The actual order-`n` vacuum-free Dyson coefficient, with the external
field labels fixed, is an explicit finite sum over all independent
preconnected local external-block diagrams and their interaction-vertex
assignments. The canonical assembly equivalence ensures that each physical
Wick diagram appears exactly once; the external-label indicator excludes
precisely the assembled diagrams with different prescribed insertions.
The shuffle/integral product decomposition is a separate subsequent step. -/
theorem vacuumFreeExternalInsertionDysonCoefficient_eq_sum_connectedBlockFamilies
    {K n : ℕ} (anchor : Fin (2 * K))
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * K) → ExternalFieldLabel Mode)
    (times : Fin (2 * K) → ℝ) :
    vacuumFreeExternalInsertionDysonCoefficient ε β g labels times n =
      ∑ p ∈ ExternalInsertionBlockLayout.connectedAssemblyFiniteDomain
          (E := K) (N := n) (ExternalLabel := ExternalFieldLabel Mode)
          (InternalLabel := QuarticVertexLabel Mode) anchor,
        if (ExternalInsertionBlockLayout.assembleConnectedBlockFamily p).1.externalLabel =
            labels then
          ExternalInsertionWickDiagram.dysonAmplitude
            (ExternalInsertionBlockLayout.assembleConnectedBlockFamily p).1
            ε β g times
        else 0 := by
  classical
  rw [vacuumFreeExternalInsertionDysonCoefficient_eq_sum_if]
  exact ExternalInsertionBlockLayout.sum_vacuumFree_eq_sum_connectedBlockFamilies
    (ExternalLabel := ExternalFieldLabel Mode)
    (InternalLabel := QuarticVertexLabel Mode) anchor
    (fun d : ExternalInsertionWickDiagram Mode K n =>
      if d.externalLabel = labels then d.dysonAmplitude ε β g times else 0)

open Classical in
/-- For a *fixed physical external-component partition*, the actual
fixed-external-label Dyson diagram fiber is reindexed by independent
connected block families with exactly that prescribed source partition.
The external-field-label condition is retained on the assembled diagram;
the integration amplitudes themselves are not yet factorized. -/
theorem sum_fixedExternalPartitionFiber_eq_sum_connectedBlockFamilies
    {K n : ℕ} (anchor : Fin (2 * K))
    (π : Finpartition (Finset.univ : Finset (Fin (2 * K))))
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * K) → ExternalFieldLabel Mode)
    (times : Fin (2 * K) → ℝ) :
    (∑ d : VacuumFreeFixedExternalInsertionWickDiagram Mode K n labels,
      if externalComponentPartition d.1.1.vertexGraph = π then
        d.1.1.dysonAmplitude ε β g times else 0) =
      ∑ p ∈ ExternalInsertionBlockLayout.connectedAssemblyFiniteDomain
          (E := K) (N := n) (ExternalLabel := ExternalFieldLabel Mode)
          (InternalLabel := QuarticVertexLabel Mode) anchor,
        if p.1.partition = π then
          if (ExternalInsertionBlockLayout.assembleConnectedBlockFamily p).1.externalLabel =
              labels then
            ExternalInsertionWickDiagram.dysonAmplitude
              (ExternalInsertionBlockLayout.assembleConnectedBlockFamily p).1
              ε β g times
          else 0
        else 0 := by
  classical
  have hFixed :=
    sum_vacuumFreeFixedExternalInsertionWickDiagram_eq_sum_if
      (Mode := Mode) labels (fun d : ExternalInsertionWickDiagram Mode K n =>
        if externalComponentPartition d.vertexGraph = π then
          d.dysonAmplitude ε β g times else 0)
  calc
    (∑ d : VacuumFreeFixedExternalInsertionWickDiagram Mode K n labels,
      if externalComponentPartition d.1.1.vertexGraph = π then
        d.1.1.dysonAmplitude ε β g times else 0) =
      ∑ d : {d : ExternalInsertionWickDiagram Mode K n //
          HasNoVacuumComponent d.vertexGraph},
        if d.1.externalLabel = labels then
          if externalComponentPartition d.1.vertexGraph = π then
            d.1.dysonAmplitude ε β g times else 0
        else 0 := by
      exact hFixed
    _ = ∑ d : {d : ExternalInsertionWickDiagram Mode K n //
          HasNoVacuumComponent d.vertexGraph},
        if externalComponentPartition d.1.vertexGraph = π then
          if d.1.externalLabel = labels then
            d.1.dysonAmplitude ε β g times else 0
        else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      by_cases hp : externalComponentPartition d.1.vertexGraph = π <;> simp [hp]
    _ = _ :=
      ExternalInsertionBlockLayout.sum_externalPartitionFiber_eq_sum_connectedBlockFamilies
        (ExternalLabel := ExternalFieldLabel Mode)
        (InternalLabel := QuarticVertexLabel Mode) anchor π
        (fun d : ExternalInsertionWickDiagram Mode K n =>
          if d.externalLabel = labels then d.dysonAmplitude ε β g times else 0)

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

/-- For any nonempty family of external insertions, the **actual**
fixed-label connected Dyson coefficient is exactly the top external-partition
fiber of the vacuum-free diagram sum.

No quotient by vacuum diagrams or formal cumulant inversion is used here:
connectivity is identified with the genuine graph-induced external partition
of each Wick pairing. -/
theorem connectedExternalInsertionDysonCoefficient_eq_topPartitionFiber
    {K : ℕ} (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * K) → ExternalFieldLabel Mode)
    (times : Fin (2 * K) → ℝ) (n : ℕ)
    (anchor : Fin (2 * K)) :
    connectedExternalInsertionDysonCoefficient ε β g labels times n =
      ∑ d : VacuumFreeFixedExternalInsertionWickDiagram Mode K n labels,
        if externalComponentPartition d.1.1.vertexGraph = ⊤ then
          d.1.1.dysonAmplitude ε β g times else 0 := by
  classical
  unfold connectedExternalInsertionDysonCoefficient
  apply Finset.sum_congr
  · ext d
    simp
  · intro d _
    simp only [← (d.1.1.allExternalVerticesConnected_iff_externalComponentPartition_eq_top anchor)]

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

/-- The source-subset moment is the vacuum-normalized *physical* vertex-Dyson
correlator for every nonempty even external subset. Multiplication by the
normalized vacuum partition series recovers the operator insertion series.
This bridge uses the existing Gibbs/Wick and Cauchy factorization theorems;
it does not assume the distinct external components are connected. -/
theorem externalSubsetMomentSeries_mul_normalizedPartition_eq_vertexDysonSeries
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (times : Fin (2 * E) → ℝ)
    (S : Finset (Fin (2 * E))) (hS : S ≠ ∅) (heven : Even S.card) :
    externalSubsetMomentSeries ε β g labels times S *
        PowerSeries.normalizeByConstantCoeff
          (Common.dysonTraceSeries (fermionEnergy ε) β (quarticInteraction g)) =
      externalInsertionVertexDysonSeries ε β 0 g
        (evenExternalSubsetLabels labels S heven)
        (evenExternalSubsetTimes times S heven) := by
  have hm : externalSubsetMomentSeries ε β g labels times S =
      vacuumFreeExternalInsertionDysonSeries ε β g
        (evenExternalSubsetLabels labels S heven)
        (evenExternalSubsetTimes times S heven) := by
    simp [externalSubsetMomentSeries, hS, heven]
  rw [hm]
  exact (externalInsertionVertexDysonSeries_eq_vacuumFree_mul_normalizedDysonPartitionSeries
    ε β hβ g (evenExternalSubsetLabels labels S heven)
    (evenExternalSubsetTimes times S heven)).symm

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

/-- The signed connected-diagram partition formula has the same
vacuum normalization as the physical subset Dyson moment: it is one at
the empty source set, without assigning an empty connected diagram. -/
@[simp]
theorem externalSubsetSignedConnectedMomentSeries_empty
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (times : Fin (2 * E) → ℝ) :
    externalSubsetSignedConnectedMomentSeries ε β g labels times ∅ = 1 := by
  unfold externalSubsetSignedConnectedMomentSeries
  rw [Finpartition.weightedMomentFromCumulant_empty]
  simp [externalPartitionSourceSign_top]

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

/-- Empty and odd external subsets already satisfy the physical
signed partition identity, unconditionally. Thus completing Phase 5
requires proving that identity **only for nonempty even subsets**.

The remaining hypothesis is genuinely diagrammatic: it is not replaced
by an unsigned moment inversion or by defining the connected weights
from the moments. -/
theorem externalSubsetMomentSeries_eq_signedConnected_of_nonempty_even
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (times : Fin (2 * E) → ℝ)
    (hEven : ∀ S : Finset (Fin (2 * E)), S ≠ ∅ → Even S.card →
      externalSubsetMomentSeries ε β g labels times S =
        externalSubsetSignedConnectedMomentSeries ε β g labels times S) :
    ∀ S : Finset (Fin (2 * E)),
      externalSubsetMomentSeries ε β g labels times S =
        externalSubsetSignedConnectedMomentSeries ε β g labels times S := by
  intro S
  by_cases hEmpty : S = ∅
  · subst S
    simp
  · by_cases hParity : Even S.card
    · exact hEven S hEmpty hParity
    · rw [(externalSubsetSeries_eq_zero_of_odd ε β g labels times S hParity).1,
        externalSubsetSignedConnectedMomentSeries_eq_zero_of_odd
          ε β g labels times S hParity]

/-- The precise remaining physical bridge for Phase 5: once the actual
vacuum-normalized Wick/Dyson moments satisfy the signed external-partition
identity, the recursively defined fermionic *source cumulant* is the fully
externally connected integrated diagram sum.

This theorem uses genuine signed moment inversion; it does not assume
unsigned Möbius inversion or conflate vacuum-freeness with connectivity.
Its hypothesis is the still-required diagram-assembly/shuffle identity. -/
theorem externalSubsetSourceCumulantSeries_eq_connectedDiagramSeries_of_signedMoments
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (times : Fin (2 * E) → ℝ)
    (hDiagram : ∀ S : Finset (Fin (2 * E)),
      externalSubsetMomentSeries ε β g labels times S =
        externalSubsetSignedConnectedMomentSeries ε β g labels times S) :
    externalSubsetSourceCumulantSeries
        (externalSubsetMomentSeries ε β g labels times) =
      externalSubsetConnectedDiagramSeries ε β g labels times := by
  apply externalPartitionWeightedMoment_injective
  · simp
  · intro S
    calc
      Finpartition.weightedMomentFromCumulant
          (fun _ π => PowerSeries.C (externalPartitionSourceSign π))
          (externalSubsetSourceCumulantSeries
            (externalSubsetMomentSeries ε β g labels times)) S =
        externalSubsetMomentSeries ε β g labels times S :=
          externalSubsetSourceCumulantSeries_reconstruct
            (externalSubsetMomentSeries ε β g labels times) (by simp) S
      _ = Finpartition.weightedMomentFromCumulant
          (fun _ π => PowerSeries.C (externalPartitionSourceSign π))
          (externalSubsetConnectedDiagramSeries ε β g labels times) S := hDiagram S


end Fermionic
end SecondQuantization
