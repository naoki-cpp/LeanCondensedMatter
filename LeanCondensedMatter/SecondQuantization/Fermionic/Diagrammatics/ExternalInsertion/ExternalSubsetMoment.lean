import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ExternalSubsetAssembly

set_option linter.style.header false

/-!
# Fermionic external-subset moments and connected-diagram contributions

Reindex vacuum-free fixed-label Dyson coefficients by external-component
partitions and local connected-block families. Define the physical
vacuum-normalized subset moments and their connected-source cumulants.
The source-order and assembly results come from ExternalSubsetAssembly.
-/

namespace SecondQuantization
namespace Fermionic

open Common
open scoped BigOperators

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {E : ℕ}

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
  exact Finset.sum_congr (by ext d; simp) (fun _ _ => rfl)

/-- A physical vacuum-free Wick diagram can never have an external
connected component with an odd number of fermion insertions. Therefore
the *actual integrated Dyson partition fiber* at an odd-block partition
vanishes term by term, without a cancellation or cumulant assumption. -/
theorem fixedExternalPartitionDysonFiber_eq_zero_of_oddBlock
    {K n : ℕ} (π : Finpartition (Finset.univ : Finset (Fin (2 * K))))
    (B : π.parts) (hodd : ¬ Even (B : Finset (Fin (2 * K))).card)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * K) → ExternalFieldLabel Mode)
    (times : Fin (2 * K) → ℝ) :
    (∑ d : VacuumFreeFixedExternalInsertionWickDiagram Mode K n labels,
      if externalComponentPartition d.1.1.vertexGraph = π then
        d.1.1.dysonAmplitude ε β g times else 0) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro d _
  by_cases hp : externalComponentPartition d.1.1.vertexGraph = π
  · exact (hodd (d.1.1.externalComponentPartition_block_card_even B.1
      (by rw [hp]; exact B.2))).elim
  · simp only [hp, ↓reduceIte]

/-- The **physical** vacuum-free Dyson coefficient is supported only on
external partitions with even block cardinalities. This is the required
fermion-parity reduction *before* the physical fixed-partition layout and
shuffle reindexing; arbitrary odd-block partitions are not silently
discarded. -/
theorem vacuumFreeExternalInsertionDysonCoefficient_eq_sum_evenPartitionFibers
    {K : ℕ} (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * K) → ExternalFieldLabel Mode)
    (times : Fin (2 * K) → ℝ) (n : ℕ) :
    vacuumFreeExternalInsertionDysonCoefficient ε β g labels times n =
      ∑ π : Finpartition (Finset.univ : Finset (Fin (2 * K))),
        if ∀ B : π.parts, Even (B : Finset (Fin (2 * K))).card then
          ∑ d : VacuumFreeFixedExternalInsertionWickDiagram Mode K n labels,
            if externalComponentPartition d.1.1.vertexGraph = π then
              d.1.1.dysonAmplitude ε β g times else 0
        else 0 := by
  classical
  rw [vacuumFreeExternalInsertionDysonCoefficient_eq_sum_externalPartitionFibers]
  refine Finset.sum_congr rfl fun π _ => ?_
  split_ifs with heven
  · rfl
  · obtain ⟨B, hodd⟩ := not_forall.mp heven
    exact fixedExternalPartitionDysonFiber_eq_zero_of_oddBlock
      π B hodd ε β g labels times

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
/-- Impose the physical external-component partition on a fixed-label sum
before transporting it to the unrestricted vacuum-free diagram domain. -/
private theorem sum_vacuumFreeFixedExternalInsertionWickDiagram_partition
    {K n : ℕ} {M : Type*} [AddCommMonoid M]
    (π : Finpartition (Finset.univ : Finset (Fin (2 * K))))
    (labels : Fin (2 * K) → ExternalFieldLabel Mode)
    (weight : ExternalInsertionWickDiagram Mode K n → M) :
    (∑ d : VacuumFreeFixedExternalInsertionWickDiagram Mode K n labels,
      if externalComponentPartition d.1.1.vertexGraph = π then
        weight d.1.1 else 0) =
      ∑ d : {d : ExternalInsertionWickDiagram Mode K n //
          HasNoVacuumComponent d.vertexGraph},
        if externalComponentPartition d.1.vertexGraph = π then
          if d.1.externalLabel = labels then weight d.1 else 0
        else 0 := by
  classical
  rw [sum_vacuumFreeFixedExternalInsertionWickDiagram_eq_sum_if
    (Mode := Mode) labels
      (fun d : ExternalInsertionWickDiagram Mode K n =>
        if externalComponentPartition d.vertexGraph = π then weight d else 0)]
  exact Finset.sum_congr rfl (by intros; split_ifs <;> simp_all)

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
  exact (sum_vacuumFreeFixedExternalInsertionWickDiagram_partition
    π labels (fun d : ExternalInsertionWickDiagram Mode K n =>
      d.dysonAmplitude ε β g times)).trans
    (ExternalInsertionBlockLayout.sum_externalPartitionFiber_eq_sum_connectedBlockFamilies
      (ExternalLabel := ExternalFieldLabel Mode)
      (InternalLabel := QuarticVertexLabel Mode) anchor π
      (fun d : ExternalInsertionWickDiagram Mode K n =>
        if d.externalLabel = labels then d.dysonAmplitude ε β g times else 0))

/-- The exact physical fixed-partition Dyson fiber can be enumerated using only
the independently specified local external-source labels. The test of the
*assembled* global label family is equivalent to a separate label test on
every source-partition block. This is needed before summing independently
labelled connected Dyson coefficients, and remains valid for blocks with
no interaction vertices. -/
theorem sum_fixedExternalPartitionFiber_eq_sum_localLabelConnectedBlockFamilies
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
          if ∀ B : p.1.partition.parts,
              (p.2.1 B).externalLabel =
                fun i => labels (p.1.sourceEquiv.symm ⟨B, i⟩) then
            ExternalInsertionWickDiagram.dysonAmplitude
              (ExternalInsertionBlockLayout.assembleConnectedBlockFamily p).1
              ε β g times
          else 0
        else 0 := by
  classical
  rw [sum_fixedExternalPartitionFiber_eq_sum_connectedBlockFamilies
    anchor π ε β g labels times]
  apply Finset.sum_congr rfl
  rintro ⟨layout, ⟨F, _⟩⟩ _
  simp only [ExternalInsertionBlockLayout.assembleConnectedBlockFamily,
    layout.assembleDiagram_externalLabel_eq_iff (Finset.univ : Finset (Fin n)) F labels]

/-- The canonical physical Dyson integral of an independently
assembled Wick diagram is precisely the ordered Dyson amplitude for
the block-local orders induced by the increasing ambient order and
the *actual* interaction-assignment shuffle. This identifies the
canonical term among the global order/shuffle terms without asserting
that a single ordered-simplex integral factors over blocks. -/
theorem ExternalInsertionBlockLayout.assembleDiagram_dysonAmplitude_eq_assignmentOrdered
    {n : ℕ} (layout : ExternalInsertionBlockLayout E n)
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram (ExternalFieldLabel Mode) (QuarticVertexLabel Mode)
        ((B : Finset (Fin (2 * E))).card / 2) n
        (layout.interactionBlock (Finset.univ : Finset (Fin n)) B))
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (times : Fin (2 * E) → ℝ) :
    ExternalInsertionWickDiagram.dysonAmplitude
        (layout.assembleDiagram (Finset.univ : Finset (Fin n)) F) ε β g times =
      ExternalInsertionWickDiagram.orderedDysonAmplitude
        (layout.assembleDiagram (Finset.univ : Finset (Fin n)) F) ε β g times
        (layout.interactionOrderDecompositionEquiv.symm
          ((layout.interactionOrderDecompositionEquiv
            ((Finset.univ : Finset (Fin n)).orderIsoOfFin rfl).toEquiv).1,
            layout.interactionAssignmentShuffle)) := by
  simpa only [ExternalInsertionBlockLayout.interactionAssignmentShuffle,
    Prod.mk.eta, Equiv.symm_apply_apply] using
    (ExternalInsertionWickDiagram.orderedDysonAmplitude_canonicalOrder
      (layout.assembleDiagram (Finset.univ : Finset (Fin n)) F)
      ε β g times).symm

open Classical in
/-- The actual integrated, fixed-source-label Dyson coefficient in one
even external-component partition is reindexed by the physical interaction
cardinalities and their unique owner shuffle, together with independently
preconnected local labelled Wick diagrams. Each summand remains the
*actual assembled physical Dyson amplitude*; the further shuffle-orbit
summation is needed before its local integrals can be multiplied. -/
theorem sum_fixedExternalPartitionDysonFiber_eq_sizes_shuffles
    {K n : ℕ} (anchor : Fin (2 * K))
    (π : Finpartition (Finset.univ : Finset (Fin (2 * K))))
    (heven : ∀ B : π.parts, Even (B : Finset (Fin (2 * K))).card)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * K) → ExternalFieldLabel Mode)
    (times : Fin (2 * K) → ℝ) :
    (∑ d : VacuumFreeFixedExternalInsertionWickDiagram Mode K n labels,
      if externalComponentPartition d.1.1.vertexGraph = π then
        d.1.1.dysonAmplitude ε β g times else 0) =
      ∑ p ∈ ExternalInsertionBlockLayout.fixedPartitionPhysicalSizeShuffleFiniteDomain
          (E := K) (N := n) (ExternalLabel := ExternalFieldLabel Mode)
          (InternalLabel := QuarticVertexLabel Mode) anchor π heven,
        if (((ExternalInsertionBlockLayout.fixedPartitionPhysicalSizeShuffleEquiv
            (E := K) (N := n) (ExternalLabel := ExternalFieldLabel Mode)
            (InternalLabel := QuarticVertexLabel Mode)
            anchor π heven).symm p).1.1).externalLabel = labels then
          ExternalInsertionWickDiagram.dysonAmplitude
            (((ExternalInsertionBlockLayout.fixedPartitionPhysicalSizeShuffleEquiv
              (E := K) (N := n) (ExternalLabel := ExternalFieldLabel Mode)
              (InternalLabel := QuarticVertexLabel Mode)
              anchor π heven).symm p).1.1) ε β g times
        else 0 := by
  classical
  exact (sum_vacuumFreeFixedExternalInsertionWickDiagram_partition
    π labels (fun d : ExternalInsertionWickDiagram Mode K n =>
      d.dysonAmplitude ε β g times)).trans
    (ExternalInsertionBlockLayout.sum_vacuumFree_fixedPartition_eq_sizes_shuffles
      (E := K) (N := n) anchor π heven
      (fun d : ExternalInsertionWickDiagram Mode K n =>
        if d.externalLabel = labels then d.dysonAmplitude ε β g times else 0))

open Classical in
/-- A physical, integrated fixed-label Dyson partition fiber is a finite
sum over the unique owner size/shuffle data and independently connected
local Wick diagrams, with the source-label predicate imposed *blockwise*
in the canonical increasing external-slot order. This is the form needed
to compare the physical owner-shuffle sum with the previously proved
summed connected-block Dyson shuffle orbit. No amplitude has been
factorized at the level of an individual ordered-simplex integral. -/
theorem sum_fixedExternalPartitionDysonFiber_eq_sizes_shuffles_localLabels
    {K n : ℕ} (anchor : Fin (2 * K))
    (π : Finpartition (Finset.univ : Finset (Fin (2 * K))))
    (heven : ∀ B : π.parts, Even (B : Finset (Fin (2 * K))).card)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * K) → ExternalFieldLabel Mode)
    (times : Fin (2 * K) → ℝ) :
    (∑ d : VacuumFreeFixedExternalInsertionWickDiagram Mode K n labels,
      if externalComponentPartition d.1.1.vertexGraph = π then
        d.1.1.dysonAmplitude ε β g times else 0) =
      ∑ p ∈ ExternalInsertionBlockLayout.fixedPartitionPhysicalSizeShuffleFiniteDomain
          (E := K) (N := n) (ExternalLabel := ExternalFieldLabel Mode)
          (InternalLabel := QuarticVertexLabel Mode) anchor π heven,
        let layout : ExternalInsertionBlockLayout K n :=
          ((ExternalInsertionBlockLayout.fixedPartitionSizeShuffleEquiv
            (E := K) (N := n) π heven).symm p.1).1
        if ∀ B : layout.partition.parts,
            (p.2.1 B).externalLabel =
              evenExternalSubsetLabels labels (B : Finset (Fin (2 * K)))
                (layout.evenBlocks B) then
          ExternalInsertionWickDiagram.dysonAmplitude
            (layout.assembleDiagram (Finset.univ : Finset (Fin n)) p.2.1)
            ε β g times
        else 0 := by
  classical
  rw [sum_fixedExternalPartitionDysonFiber_eq_sizes_shuffles
    anchor π heven ε β g labels times]
  apply Finset.sum_congr rfl
  intro p _
  let layout : ExternalInsertionBlockLayout K n :=
    ((ExternalInsertionBlockLayout.fixedPartitionSizeShuffleEquiv
      (E := K) (N := n) π heven).symm p.1).1
  rw [ExternalInsertionBlockLayout.fixedPartitionPhysicalSizeShuffleEquiv_symm_diagram
    (E := K) (N := n) anchor π heven p]
  exact if_congr
    (ExternalInsertionBlockLayout.assembleDiagram_externalLabel_eq_iff_evenSubsetLabels
      layout p.2.1 labels) rfl rfl

open Classical in
/-- At fixed perturbation order and fixed physical external partition,
the genuine vacuum-free Dyson coefficient is a finite sum of *ordered*
Dyson amplitudes indexed by the exact physical owner size/shuffle
assignment. The local source labels are imposed blockwise; each
assembled diagram carries the local interaction orders induced by the
increasing ambient vertex order, rather than any extra permutations.
This is the coefficient-level endpoint of the purely combinatorial
reindexing, before identifying different owner shuffles with a single
physical diagram's full integrated shuffle orbit. -/
theorem sum_fixedExternalPartitionDysonFiber_eq_assignmentOrderedDyson
    {K n : ℕ} (anchor : Fin (2 * K))
    (π : Finpartition (Finset.univ : Finset (Fin (2 * K))))
    (heven : ∀ B : π.parts, Even (B : Finset (Fin (2 * K))).card)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * K) → ExternalFieldLabel Mode)
    (times : Fin (2 * K) → ℝ) :
    (∑ d : VacuumFreeFixedExternalInsertionWickDiagram Mode K n labels,
      if externalComponentPartition d.1.1.vertexGraph = π then
        d.1.1.dysonAmplitude ε β g times else 0) =
      ∑ p ∈ ExternalInsertionBlockLayout.fixedPartitionPhysicalSizeShuffleFiniteDomain
          (E := K) (N := n) (ExternalLabel := ExternalFieldLabel Mode)
          (InternalLabel := QuarticVertexLabel Mode) anchor π heven,
        let layout : ExternalInsertionBlockLayout K n :=
          ((ExternalInsertionBlockLayout.fixedPartitionSizeShuffleEquiv
            (E := K) (N := n) π heven).symm p.1).1
        if ∀ B : layout.partition.parts,
            (p.2.1 B).externalLabel =
              evenExternalSubsetLabels labels (B : Finset (Fin (2 * K)))
                (layout.evenBlocks B) then
          ExternalInsertionWickDiagram.orderedDysonAmplitude
            (layout.assembleDiagram (Finset.univ : Finset (Fin n)) p.2.1)
            ε β g times
            (layout.interactionOrderDecompositionEquiv.symm
              ((layout.interactionOrderDecompositionEquiv
                ((Finset.univ : Finset (Fin n)).orderIsoOfFin rfl).toEquiv).1,
                layout.interactionAssignmentShuffle))
        else 0 := by
  classical
  rw [sum_fixedExternalPartitionDysonFiber_eq_sizes_shuffles_localLabels
    anchor π heven ε β g labels times]
  simp only [ExternalInsertionBlockLayout.assembleDiagram_dysonAmplitude_eq_assignmentOrdered]

/-- The full fixed-order physical Dyson coefficient is reindexed by even
external-component partitions and independently labelled connected blocks.
The owner assignments and genuine assembled Dyson amplitudes are retained:
the remaining factorization must still sum those assignments and their
ordered interaction shuffles. -/
theorem vacuumFreeExternalInsertionDysonCoefficient_eq_sum_evenPartitions_localLabelFamilies
    {K n : ℕ} (anchor : Fin (2 * K))
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * K) → ExternalFieldLabel Mode)
    (times : Fin (2 * K) → ℝ) :
    vacuumFreeExternalInsertionDysonCoefficient ε β g labels times n =
      ∑ π : Finpartition (Finset.univ : Finset (Fin (2 * K))),
        if ∀ B : π.parts, Even (B : Finset (Fin (2 * K))).card then
          ∑ p ∈ ExternalInsertionBlockLayout.connectedAssemblyFiniteDomain
              (E := K) (N := n) (ExternalLabel := ExternalFieldLabel Mode)
              (InternalLabel := QuarticVertexLabel Mode) anchor,
            if p.1.partition = π then
              if ∀ B : p.1.partition.parts,
                  (p.2.1 B).externalLabel =
                    fun i => labels (p.1.sourceEquiv.symm ⟨B, i⟩) then
                ExternalInsertionWickDiagram.dysonAmplitude
                  (ExternalInsertionBlockLayout.assembleConnectedBlockFamily p).1
                  ε β g times
              else 0
            else 0
        else 0 := by
  classical
  rw [vacuumFreeExternalInsertionDysonCoefficient_eq_sum_evenPartitionFibers]
  simp_rw [sum_fixedExternalPartitionFiber_eq_sum_localLabelConnectedBlockFamilies anchor]

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
  apply Finset.sum_congr (by ext d; simp)
  intro d _
  simp only [← (d.1.1.allExternalVerticesConnected_iff_externalComponentPartition_eq_top anchor)]

/-- The formal Dyson series of the fully external-connected diagram sector.
It is not identified with a source cumulant without the signed moment theorem. -/
noncomputable def connectedExternalInsertionDysonSeries {K : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * K) → ExternalFieldLabel Mode)
    (times : Fin (2 * K) → ℝ) : PowerSeries ℂ :=
  PowerSeries.mk (connectedExternalInsertionDysonCoefficient ε β g labels times)

/-- With exactly two external fermion insertions, every physical Wick pairing
connects both external vertices. Removing vacuum components therefore already
selects the fully externally connected diagrams, coefficient by coefficient.
This does not identify the independent legacy two-point diagram model. -/
theorem vacuumFreeExternalInsertionDysonCoefficient_eq_connected_two
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin 2 → ExternalFieldLabel Mode)
    (times : Fin 2 → ℝ) (n : ℕ) :
    vacuumFreeExternalInsertionDysonCoefficient (E := 1) ε β g labels times n =
      connectedExternalInsertionDysonCoefficient (K := 1) ε β g labels times n := by
  classical
  unfold vacuumFreeExternalInsertionDysonCoefficient
    connectedExternalInsertionDysonCoefficient
  apply Finset.sum_congr (by ext d; simp)
  intro d _
  simp only [d.1.1.allExternalVerticesConnected_two, ↓reduceIte]

/-- At two external insertions, the *physical* vacuum-free Dyson series
and the fully externally connected diagram series agree without a signed
partition-moment hypothesis, at every perturbative order. -/
theorem vacuumFreeExternalInsertionDysonSeries_eq_connected_two
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin 2 → ExternalFieldLabel Mode)
    (times : Fin 2 → ℝ) :
    vacuumFreeExternalInsertionDysonSeries (E := 1) ε β g labels times =
      connectedExternalInsertionDysonSeries (K := 1) ε β g labels times := by
  unfold vacuumFreeExternalInsertionDysonSeries connectedExternalInsertionDysonSeries
  exact congrArg PowerSeries.mk (funext fun n =>
    vacuumFreeExternalInsertionDysonCoefficient_eq_connected_two
      ε β g labels times n)

/-- The physical vacuum-free and connected Dyson series agree for any
external pair count *proved equal* to one; this dependent form avoids
casts in the source-subset moment theorem. -/
theorem vacuumFreeExternalInsertionDysonSeries_eq_connected_of_single_pair
    {K : ℕ} (hK : K = 1)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * K) → ExternalFieldLabel Mode)
    (times : Fin (2 * K) → ℝ) :
    vacuumFreeExternalInsertionDysonSeries ε β g labels times =
      connectedExternalInsertionDysonSeries ε β g labels times := by
  subst K
  exact vacuumFreeExternalInsertionDysonSeries_eq_connected_two ε β g labels times

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
  simpa [externalSubsetMomentSeries, hS, heven] using
    (externalInsertionVertexDysonSeries_eq_vacuumFree_mul_normalizedDysonPartitionSeries
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
  obtain ⟨B, hB, hBodd⟩ : ∃ B ∈ π.parts, ¬ Even B.card := by
    by_contra! h
    apply hodd
    rw [← π.sum_card_parts]
    exact Finset.even_sum (s := π.parts)
      (fun B : Finset (Fin (2 * E)) => B.card) h
  rw [Finpartition.partitionProduct,
    Finset.prod_eq_zero hB
      (externalSubsetSeries_eq_zero_of_odd ε β g labels times B hBodd).2,
    mul_zero]

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

/-- The *physical* signed external-source moment identity holds
unconditionally for two external fermion insertions. A nonempty even
subset of two slots has cardinality two, and every proper nonempty
subset is odd. The only surviving term is therefore the connected
top-partition term, which equals the vacuum-free Dyson series by the
actual two-insertion graph theorem. -/
theorem externalSubsetMomentSeries_eq_signedConnected_two
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin 2 → ExternalFieldLabel Mode)
    (times : Fin 2 → ℝ) :
    ∀ S : Finset (Fin 2),
      externalSubsetMomentSeries (E := 1) ε β g labels times S =
        externalSubsetSignedConnectedMomentSeries (E := 1) ε β g labels times S := by
  classical
  apply externalSubsetMomentSeries_eq_signedConnected_of_nonempty_even
    (E := 1) ε β g labels times
  intro S hEmpty hEven
  have hcard : S.card = 2 := by
    have hpos : 0 < S.card :=
      Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hEmpty)
    have hle : S.card ≤ 2 := by
      simpa using Finset.card_le_card (Finset.subset_univ S)
    obtain ⟨k, hk⟩ := hEven
    omega
  have hproper :
      ∀ B : Finset (Fin 2), B ⊂ S →
        externalSubsetConnectedDiagramSeries (E := 1) ε β g labels times B = 0 := by
    intro B hB
    have hlt := Finset.card_lt_card hB
    have hBcard : B.card = 0 ∨ B.card = 1 := by omega
    rcases hBcard with hzero | hone
    · simp [Finset.card_eq_zero.mp hzero, externalSubsetConnectedDiagramSeries]
    · exact (externalSubsetSeries_eq_zero_of_odd (E := 1)
        ε β g labels times B (by simp [hone])).2
  have hweighted :
      externalSubsetSignedConnectedMomentSeries (E := 1) ε β g labels times S =
        externalSubsetConnectedDiagramSeries (E := 1) ε β g labels times S := by
    unfold externalSubsetSignedConnectedMomentSeries
    exact externalPartitionWeightedMoment_eq_of_proper_zero (E := 1)
      (externalSubsetConnectedDiagramSeries (E := 1) ε β g labels times)
      S hEmpty hproper
  have hphysical :
      externalSubsetMomentSeries (E := 1) ε β g labels times S =
        externalSubsetConnectedDiagramSeries (E := 1) ε β g labels times S := by
    simp only [externalSubsetMomentSeries, externalSubsetConnectedDiagramSeries,
      hEmpty, hEven, dite_eq_left]
    exact vacuumFreeExternalInsertionDysonSeries_eq_connected_of_single_pair
      (show S.card / 2 = 1 by omega) ε β g
      (evenExternalSubsetLabels (E := 1) labels S hEven)
      (evenExternalSubsetTimes (E := 1) times S hEven)
  exact hphysical.trans hweighted.symm

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
    exact (externalSubsetSourceCumulantSeries_reconstruct
      (externalSubsetMomentSeries ε β g labels times) (by simp) S).trans (hDiagram S)


/-- The actual two-insertion source cumulant equals the fully
externally connected physical Dyson series at all perturbative
orders, with no signed-moment hypothesis. This is the two-insertion
specialization; higher external sectors still need the shuffle
covariance theorem. -/
theorem externalSubsetSourceCumulantSeries_eq_connectedDiagramSeries_two
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin 2 → ExternalFieldLabel Mode)
    (times : Fin 2 → ℝ) :
    externalSubsetSourceCumulantSeries (E := 1)
        (externalSubsetMomentSeries (E := 1) ε β g labels times) =
      externalSubsetConnectedDiagramSeries (E := 1) ε β g labels times := by
  exact externalSubsetSourceCumulantSeries_eq_connectedDiagramSeries_of_signedMoments
    (E := 1) ε β g labels times
    (externalSubsetMomentSeries_eq_signedConnected_two ε β g labels times)


end Fermionic
end SecondQuantization
