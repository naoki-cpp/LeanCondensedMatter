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

This identity only partitions the sum into physical diagram fibers;
it makes no amplitude factorization assumption. -/
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
The identity retains the original Dyson amplitudes and interaction ordering. -/
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
  rw [sum_vacuumFreeFixedExternalInsertionWickDiagram_partition
    π labels (fun d : ExternalInsertionWickDiagram Mode K n =>
      d.dysonAmplitude ε β g times)]
  rw [ExternalInsertionBlockLayout.sum_externalPartitionFiber_eq_sum_connectedBlockFamilies
    (ExternalLabel := ExternalFieldLabel Mode)
    (InternalLabel := QuarticVertexLabel Mode) anchor π
    (fun d : ExternalInsertionWickDiagram Mode K n =>
      if d.externalLabel = labels then d.dysonAmplitude ε β g times else 0)]
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
/-- A physical, integrated fixed-label Dyson partition fiber is a finite
sum over the unique owner size/shuffle data and independently connected
local Wick diagrams, with the source-label predicate imposed *blockwise*
in the canonical increasing external-slot order. The expression
retains the physical owner-shuffle sum and connected-block Dyson
amplitudes without factorizing individual ordered-simplex integrals. -/
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
  rw [sum_vacuumFreeFixedExternalInsertionWickDiagram_partition
    π labels (fun d : ExternalInsertionWickDiagram Mode K n =>
      d.dysonAmplitude ε β g times)]
  rw [ExternalInsertionBlockLayout.sum_vacuumFree_fixedPartition_eq_sizes_shuffles
    (E := K) (N := n) anchor π heven
    (fun d : ExternalInsertionWickDiagram Mode K n =>
      if d.externalLabel = labels then d.dysonAmplitude ε β g times else 0)]
  apply Finset.sum_congr rfl
  intro p _
  let layout : ExternalInsertionBlockLayout K n :=
    ((ExternalInsertionBlockLayout.fixedPartitionSizeShuffleEquiv
      (E := K) (N := n) π heven).symm p.1).1
  rw [ExternalInsertionBlockLayout.fixedPartitionPhysicalSizeShuffleEquiv_symm_diagram
    (E := K) (N := n) anchor π heven p]
  exact if_congr
    (layout.assembleDiagram_externalLabel_eq_iff
      (Finset.univ : Finset (Fin n)) p.2.1 labels) rfl rfl

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

/-- The finite set of interaction-size vectors realizable by an actual
assignment of the `n` ambient interaction slots to the blocks of `π`.
Each vector is counted once, independently of the number of shuffles
realizing it. Zero-interaction blocks are retained. -/
noncomputable def ExternalInsertionBlockLayout.realizableInteractionSizeVectors
    {K n : ℕ}
    (π : Finpartition (Finset.univ : Finset (Fin (2 * K)))) :
    Finset (π.parts → ℕ) := by
  classical
  exact (Finset.univ : Finset (Fin n → π.parts)).image
    (fun owner =>
      ((Combinatorics.ownerSizeShuffleEquiv (ι := π.parts) (total := n)) owner).1)

/-- A size vector occurs in the finite owner-assignment domain precisely
when at least one order-preserving owner shuffle realizes it. -/
theorem ExternalInsertionBlockLayout.mem_realizableInteractionSizeVectors
    {K n : ℕ}
    (π : Finpartition (Finset.univ : Finset (Fin (2 * K))))
    (size : π.parts → ℕ) :
    size ∈ ExternalInsertionBlockLayout.realizableInteractionSizeVectors (n := n) π ↔
      Nonempty (Combinatorics.FamilySlotShuffleTo size n) := by
  classical
  let e := Combinatorics.ownerSizeShuffleEquiv (ι := π.parts) (total := n)
  change size ∈ (Finset.univ : Finset (Fin n → π.parts)).image
      (fun owner => (e owner).1) ↔ _
  constructor
  · intro hs
    obtain ⟨owner, _, howner⟩ := Finset.mem_image.mp hs
    change (e owner).1 = size at howner
    cases howner
    exact ⟨(e owner).2⟩
  · rintro ⟨σ⟩
    apply Finset.mem_image.mpr
    refine ⟨e.symm ⟨size, σ⟩, Finset.mem_univ _, ?_⟩
    exact congrArg Sigma.fst (e.apply_symm_apply ⟨size, σ⟩)

/-- A realizable family of interaction orders is exactly a natural
degree distribution whose sum is the total Dyson order. The converse
uses the existing canonical family-order decomposition, including
zero-size fibers; it does not choose an extra shuffle in the sum. -/
theorem ExternalInsertionBlockLayout.mem_realizableInteractionSizeVectors_iff_sum
    {K n : ℕ}
    (π : Finpartition (Finset.univ : Finset (Fin (2 * K))))
    (size : π.parts → ℕ) :
    size ∈ ExternalInsertionBlockLayout.realizableInteractionSizeVectors (n := n) π ↔
      ∑ B : π.parts, size B = n := by
  classical
  rw [ExternalInsertionBlockLayout.mem_realizableInteractionSizeVectors]
  constructor
  · rintro ⟨σ⟩
    simpa [Fintype.card_sigma] using (Fintype.card_congr σ.slotEquiv)
  · intro hsum
    let α := Σ B : π.parts, Fin (size B)
    have hcard : Fintype.card (Fin n) = Fintype.card α := by
      simpa [α] using hsum.symm
    let order : Fin n ≃ α := Fintype.equivOfCardEq hcard
    let dec := Combinatorics.familyOrderDecompositionEquivOfSize
      (F := fun B : π.parts => Fin (size B)) (α := α) (total := n)
      size (fun B => by simp) (Equiv.refl α)
    exact ⟨(dec order).2⟩

/-- The physically realizable interaction-size sum is exactly the
coefficient of the formal product of independent block series.
This is the finite Cauchy convolution of Mathlib's `PowerSeries.coeff_prod`,
transported from finitely supported degree assignments to the owner's
realizable size vectors. No factorials or per-shuffle weights occur. -/
theorem ExternalInsertionBlockLayout.sum_realizableSize_coeff_prod
    {K n : ℕ}
    (π : Finpartition (Finset.univ : Finset (Fin (2 * K))))
    (f : π.parts → PowerSeries ℂ) :
    (∑ size ∈ ExternalInsertionBlockLayout.realizableInteractionSizeVectors (n := n) π,
      ∏ B : π.parts, PowerSeries.coeff (size B) (f B)) =
        PowerSeries.coeff n (∏ B : π.parts, f B) := by
  classical
  let e : (π.parts →₀ ℕ) ≃ (π.parts → ℕ) := Finsupp.equivFunOnFinite
  have hmem (l : π.parts →₀ ℕ) :
      e l ∈ ExternalInsertionBlockLayout.realizableInteractionSizeVectors (n := n) π ↔
        l ∈ (Finset.univ : Finset π.parts).finsuppAntidiag n := by
    rw [ExternalInsertionBlockLayout.mem_realizableInteractionSizeVectors_iff_sum,
      Finset.mem_finsuppAntidiag]
    constructor
    · intro hs
      refine ⟨?_, Finset.subset_univ _⟩
      simpa only [e, Finsupp.equivFunOnFinite_apply] using hs
    · rintro ⟨hs, _⟩
      simpa only [e, Finsupp.equivFunOnFinite_apply] using hs
  have himage :
      ((Finset.univ : Finset π.parts).finsuppAntidiag n).image e =
        ExternalInsertionBlockLayout.realizableInteractionSizeVectors (n := n) π := by
    ext size
    constructor
    · intro hs
      obtain ⟨l, hl, hls⟩ := Finset.mem_image.mp hs
      rw [← hls]
      exact (hmem l).2 hl
    · intro hs
      apply Finset.mem_image.mpr
      refine ⟨e.symm size, ?_, e.apply_symm_apply size⟩
      apply (hmem _).1
      simpa using hs
  calc
    _ = ∑ l ∈ (Finset.univ : Finset π.parts).finsuppAntidiag n,
          ∏ B : π.parts, PowerSeries.coeff ((e l) B) (f B) := by
      rw [← himage, Finset.sum_image]
      intro a _ b _ hab
      exact e.injective hab
    _ = ∑ l ∈ (Finset.univ : Finset π.parts).finsuppAntidiag n,
          ∏ B : π.parts, PowerSeries.coeff (l B) (f B) := by
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.prod_congr rfl
      intro B _
      simp [e]
    _ = _ := (PowerSeries.coeff_prod f n Finset.univ).symm

set_option maxHeartbeats 4000000 in
-- Dependent diagram fibers require a larger elaboration budget for fixed-size summation.
open Classical in
/-- The fixed-partition physical order-`n` Dyson fiber is the
Koszul-signed sum over realizable interaction-size vectors of products
of connected Dyson coefficients. The integrated interaction-shuffle
weights are preserved without an additional multiplicity. -/
theorem sum_fixedExternalPartitionDysonFiber_eq_sum_realizableSizes_signedProduct
    {K n : ℕ} (anchor : Fin (2 * K))
    (π : Finpartition (Finset.univ : Finset (Fin (2 * K))))
    (heven : ∀ B : π.parts, Even (B : Finset (Fin (2 * K))).card)
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * K) → ExternalFieldLabel Mode)
    (times : Fin (2 * K) → ℝ) :
    (∑ d : VacuumFreeFixedExternalInsertionWickDiagram Mode K n labels,
      if externalComponentPartition d.1.1.vertexGraph = π then
        d.1.1.dysonAmplitude ε β g times else 0) =
      ∑ size ∈ ExternalInsertionBlockLayout.realizableInteractionSizeVectors (n := n) π,
        externalPartitionSourceSign π *
          ∏ B : π.parts,
            ∑ d : {d : ExternalInsertionWickDiagram Mode
                ((B : Finset (Fin (2 * K))).card / 2) (size B) //
                d.vertexGraph.Preconnected},
              if d.1.externalLabel =
                  evenExternalSubsetLabels labels (B : Finset (Fin (2 * K))) (heven B)
              then d.1.dysonAmplitude ε β g
                (evenExternalSubsetTimes times (B : Finset (Fin (2 * K))) (heven B))
              else 0 := by
  classical
  let P := {d : {d : ExternalInsertionWickDiagram Mode K n //
      HasNoVacuumComponent d.vertexGraph} //
      externalComponentPartition d.1.vertexGraph = π}
  let e := ExternalInsertionBlockLayout.fixedPartitionPhysicalSizeShuffleEquiv
    (E := K) (N := n) (ExternalLabel := ExternalFieldLabel Mode)
    (InternalLabel := QuarticVertexLabel Mode) anchor π heven
  let sizeOf : P → π.parts → ℕ := fun d => (e d).1.1
  let sizes := ExternalInsertionBlockLayout.realizableInteractionSizeVectors (n := n) π
  let weight : P → ℂ := fun d =>
    if d.1.1.externalLabel = labels then d.1.1.dysonAmplitude ε β g times else 0
  have hmem (d : P) : sizeOf d ∈ sizes := by
    let ownerEquiv := Combinatorics.ownerSizeShuffleEquiv
      (ι := π.parts) (total := n)
    change (e d).1.1 ∈ (Finset.univ : Finset (Fin n → π.parts)).image
      (fun owner => (ownerEquiv owner).1)
    apply Finset.mem_image.mpr
    refine ⟨ownerEquiv.symm (e d).1, Finset.mem_univ _, ?_⟩
    exact congrArg Sigma.fst (ownerEquiv.apply_symm_apply (e d).1)
  have hphysical :
      (∑ d : VacuumFreeFixedExternalInsertionWickDiagram Mode K n labels,
        if externalComponentPartition d.1.1.vertexGraph = π then
          d.1.1.dysonAmplitude ε β g times else 0) =
        ∑ d : P, weight d := by
    rw [sum_vacuumFreeFixedExternalInsertionWickDiagram_partition
      π labels (fun d : ExternalInsertionWickDiagram Mode K n =>
        d.dysonAmplitude ε β g times)]
    simpa only [P, weight, Finset.sum_filter] using
      (Finset.sum_subtype
        (p := fun d : {d : ExternalInsertionWickDiagram Mode K n //
          HasNoVacuumComponent d.vertexGraph} =>
          externalComponentPartition d.1.vertexGraph = π)
        ((Finset.univ : Finset
          {d : ExternalInsertionWickDiagram Mode K n //
            HasNoVacuumComponent d.vertexGraph}).filter
          (fun d => externalComponentPartition d.1.vertexGraph = π))
        (fun _ => by simp)
        (fun d : {d : ExternalInsertionWickDiagram Mode K n //
          HasNoVacuumComponent d.vertexGraph} =>
          if d.1.externalLabel = labels then
            d.1.dysonAmplitude ε β g times else 0))
  have hgroup :
      (∑ d : P, weight d) =
        ∑ size ∈ sizes, ∑ d : {d : P // sizeOf d = size}, weight d.1 := by
    rw [(Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset P)) (t := sizes) (g := sizeOf)
      (fun d _ => hmem d) weight).symm]
    apply Finset.sum_congr rfl
    intro size _
    simpa only [Finset.sum_filter] using
      (Finset.sum_subtype
        (p := fun d : P => sizeOf d = size)
        ((Finset.univ : Finset P).filter (fun d => sizeOf d = size))
        (fun _ => by simp) weight)
  calc
    _ = ∑ d : P, weight d := hphysical
    _ = ∑ size ∈ sizes,
          ∑ d : {d : P // sizeOf d = size}, weight d.1 := hgroup
    _ = _ := by
      apply Finset.sum_congr rfl
      intro size hs
      obtain ⟨σ⟩ :=
        (ExternalInsertionBlockLayout.mem_realizableInteractionSizeVectors π size).mp hs
      exact ExternalInsertionBlockLayout.sum_physicalFixedSizeDyson_eq_signedProduct
        anchor π heven σ labels ε β hβ g times

set_option maxHeartbeats 4000000 in
-- The dependent local diagram enumerations expand inside a finite series product.
open Classical in
/-- The genuine fixed-external-partition physical Dyson coefficient is
the Koszul-signed coefficient of the product of *local preconnected Wick
diagram series*. This uses the realizable-size Cauchy bridge directly,
without introducing a separately defined generating-function model or
claiming invariance of an individual ordered-simplex integral. -/
theorem sum_fixedExternalPartitionDysonFiber_eq_signedCoeffPreconnectedSeries
    {K n : ℕ} (anchor : Fin (2 * K))
    (π : Finpartition (Finset.univ : Finset (Fin (2 * K))))
    (heven : ∀ B : π.parts, Even (B : Finset (Fin (2 * K))).card)
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * K) → ExternalFieldLabel Mode)
    (times : Fin (2 * K) → ℝ) :
    (∑ d : VacuumFreeFixedExternalInsertionWickDiagram Mode K n labels,
      if externalComponentPartition d.1.1.vertexGraph = π then
        d.1.1.dysonAmplitude ε β g times else 0) =
      externalPartitionSourceSign π *
        PowerSeries.coeff n
          (∏ B : π.parts,
            PowerSeries.mk (fun m : ℕ =>
              ∑ d : {d : ExternalInsertionWickDiagram Mode
                  ((B : Finset (Fin (2 * K))).card / 2) m //
                  d.vertexGraph.Preconnected},
                if d.1.externalLabel =
                    evenExternalSubsetLabels labels (B : Finset (Fin (2 * K))) (heven B)
                then d.1.dysonAmplitude ε β g
                  (evenExternalSubsetTimes times (B : Finset (Fin (2 * K))) (heven B))
                else 0)) := by
  classical
  let blockSeries : π.parts → PowerSeries ℂ := fun B =>
    PowerSeries.mk (fun m : ℕ =>
      ∑ d : {d : ExternalInsertionWickDiagram Mode
          ((B : Finset (Fin (2 * K))).card / 2) m //
          d.vertexGraph.Preconnected},
        if d.1.externalLabel =
            evenExternalSubsetLabels labels (B : Finset (Fin (2 * K))) (heven B)
        then d.1.dysonAmplitude ε β g
          (evenExternalSubsetTimes times (B : Finset (Fin (2 * K))) (heven B))
        else 0)
  have hcauchy :=
    ExternalInsertionBlockLayout.sum_realizableSize_coeff_prod (n := n) π blockSeries
  have hfactor :
      (∑ size ∈ ExternalInsertionBlockLayout.realizableInteractionSizeVectors (n := n) π,
        ∏ B : π.parts,
          ∑ d : {d : ExternalInsertionWickDiagram Mode
              ((B : Finset (Fin (2 * K))).card / 2) (size B) //
              d.vertexGraph.Preconnected},
            if d.1.externalLabel =
                evenExternalSubsetLabels labels (B : Finset (Fin (2 * K))) (heven B)
            then d.1.dysonAmplitude ε β g
              (evenExternalSubsetTimes times (B : Finset (Fin (2 * K))) (heven B))
            else 0) =
        PowerSeries.coeff n (∏ B : π.parts, blockSeries B) := by
    simpa only [blockSeries, PowerSeries.coeff_mk] using hcauchy
  calc
    _ = ∑ size ∈ ExternalInsertionBlockLayout.realizableInteractionSizeVectors (n := n) π,
          externalPartitionSourceSign π *
            ∏ B : π.parts,
              ∑ d : {d : ExternalInsertionWickDiagram Mode
                  ((B : Finset (Fin (2 * K))).card / 2) (size B) //
                  d.vertexGraph.Preconnected},
                if d.1.externalLabel =
                    evenExternalSubsetLabels labels (B : Finset (Fin (2 * K))) (heven B)
                then d.1.dysonAmplitude ε β g
                  (evenExternalSubsetTimes times (B : Finset (Fin (2 * K))) (heven B))
                else 0 :=
      sum_fixedExternalPartitionDysonFiber_eq_sum_realizableSizes_signedProduct
        anchor π heven ε β hβ g labels times
    _ = externalPartitionSourceSign π *
          (∑ size ∈ ExternalInsertionBlockLayout.realizableInteractionSizeVectors (n := n) π,
            ∏ B : π.parts,
              ∑ d : {d : ExternalInsertionWickDiagram Mode
                  ((B : Finset (Fin (2 * K))).card / 2) (size B) //
                  d.vertexGraph.Preconnected},
                if d.1.externalLabel =
                    evenExternalSubsetLabels labels (B : Finset (Fin (2 * K))) (heven B)
                then d.1.dysonAmplitude ε β g
                  (evenExternalSubsetTimes times (B : Finset (Fin (2 * K))) (heven B))
                else 0) := by rw [Finset.mul_sum]
    _ = externalPartitionSourceSign π *
          PowerSeries.coeff n (∏ B : π.parts, blockSeries B) :=
      congrArg (fun z : ℂ => externalPartitionSourceSign π * z) hfactor
    _ = _ := rfl

/-- The full fixed-order physical Dyson coefficient is reindexed by even
external-component partitions and independently labelled connected blocks.
The owner assignments, genuine assembled Dyson amplitudes, and ordered
interaction shuffles are kept explicitly. -/
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

set_option maxHeartbeats 4000000 in
-- The subtype reindexing traverses a dependent fixed-label Wick diagram domain.
open Classical in
/-- For a nonempty external sector, summing all preconnected physical Wick
diagrams with a fixed label indicator is the established fully externally
connected Dyson coefficient. This uses graph connectivity and finite
subtype reindexing, not an additional diagram model. -/
theorem sum_preconnectedDyson_eq_connectedCoefficient
    {K n : ℕ} (hK : 0 < K)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * K) → ExternalFieldLabel Mode)
    (times : Fin (2 * K) → ℝ) :
    (∑ d : {d : ExternalInsertionWickDiagram Mode K n //
        d.vertexGraph.Preconnected},
      if d.1.externalLabel = labels then
        d.1.dysonAmplitude ε β g times else 0) =
      connectedExternalInsertionDysonCoefficient ε β g labels times n := by
  classical
  letI : Nonempty (Fin (2 * K)) := ⟨⟨0, by omega⟩⟩
  have hpre (d : ExternalInsertionWickDiagram Mode K n) :
      d.vertexGraph.Preconnected ↔
        HasNoVacuumComponent d.vertexGraph ∧
          AllExternalVerticesConnected d.vertexGraph :=
    preconnected_iff_hasNoVacuumComponent_and_allExternalVerticesConnected d.vertexGraph
  unfold connectedExternalInsertionDysonCoefficient
  calc
    _ = ∑ d : ExternalInsertionWickDiagram Mode K n,
          if d.vertexGraph.Preconnected then
            if d.externalLabel = labels then d.dysonAmplitude ε β g times else 0
          else 0 := by
      simpa only [Finset.sum_filter] using
        (Finset.sum_subtype
          (p := fun d : ExternalInsertionWickDiagram Mode K n =>
            d.vertexGraph.Preconnected)
          ((Finset.univ : Finset (ExternalInsertionWickDiagram Mode K n)).filter
            (fun d => d.vertexGraph.Preconnected))
          (fun _ => by simp)
          (fun d : ExternalInsertionWickDiagram Mode K n =>
            if d.externalLabel = labels then d.dysonAmplitude ε β g times else 0)).symm
    _ = ∑ d : ExternalInsertionWickDiagram Mode K n,
          if HasNoVacuumComponent d.vertexGraph then
            if d.externalLabel = labels then
              if AllExternalVerticesConnected d.vertexGraph then
                d.dysonAmplitude ε β g times else 0
            else 0
          else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      have hp := hpre d
      by_cases hv : HasNoVacuumComponent d.vertexGraph
      · by_cases hc : AllExternalVerticesConnected d.vertexGraph
        · simp [hp, hv, hc]
        · simp [hp, hv, hc]
      · simp [hp, hv]
    _ = ∑ d : {d : ExternalInsertionWickDiagram Mode K n //
          HasNoVacuumComponent d.vertexGraph},
          if d.1.externalLabel = labels then
            if AllExternalVerticesConnected d.1.vertexGraph then
              d.1.dysonAmplitude ε β g times else 0
          else 0 := by
      simpa only [Finset.sum_filter] using
        (Finset.sum_subtype
          (p := fun d : ExternalInsertionWickDiagram Mode K n =>
            HasNoVacuumComponent d.vertexGraph)
          ((Finset.univ : Finset (ExternalInsertionWickDiagram Mode K n)).filter
            (fun d => HasNoVacuumComponent d.vertexGraph))
          (fun _ => by simp)
          (fun d : ExternalInsertionWickDiagram Mode K n =>
            if d.externalLabel = labels then
              if AllExternalVerticesConnected d.vertexGraph then
                d.dysonAmplitude ε β g times else 0
            else 0))
    _ = _ :=
      (sum_vacuumFreeFixedExternalInsertionWickDiagram_eq_sum_if
        labels
        (fun d : ExternalInsertionWickDiagram Mode K n =>
          if AllExternalVerticesConnected d.vertexGraph then
            d.dysonAmplitude ε β g times else 0)).symm

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
  simp only [← (allExternalVerticesConnected_iff_externalComponentPartition_eq_top d.1.1.vertexGraph anchor)]

/-- The formal Dyson series of the fully externally connected diagram sector,
defined from its physical connected-diagram coefficients. -/
noncomputable def connectedExternalInsertionDysonSeries {K : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * K) → ExternalFieldLabel Mode)
    (times : Fin (2 * K) → ℝ) : PowerSeries ℂ :=
  PowerSeries.mk (connectedExternalInsertionDysonCoefficient ε β g labels times)

set_option maxHeartbeats 4000000 in
-- The blockwise series equality elaborates dependent even external subsets.
open Classical in
/-- The integrated Dyson coefficient at a fixed external partition and
interaction order is the Koszul-signed Cauchy coefficient of the product
of connected Dyson diagram series. -/
theorem sum_fixedExternalPartitionDysonFiber_eq_signedCoeffConnectedSeries
    {K n : ℕ} (anchor : Fin (2 * K))
    (π : Finpartition (Finset.univ : Finset (Fin (2 * K))))
    (heven : ∀ B : π.parts, Even (B : Finset (Fin (2 * K))).card)
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * K) → ExternalFieldLabel Mode)
    (times : Fin (2 * K) → ℝ) :
    (∑ d : VacuumFreeFixedExternalInsertionWickDiagram Mode K n labels,
      if externalComponentPartition d.1.1.vertexGraph = π then
        d.1.1.dysonAmplitude ε β g times else 0) =
      externalPartitionSourceSign π *
        PowerSeries.coeff n
          (∏ B : π.parts,
            connectedExternalInsertionDysonSeries ε β g
              (evenExternalSubsetLabels labels (B : Finset (Fin (2 * K))) (heven B))
              (evenExternalSubsetTimes times (B : Finset (Fin (2 * K))) (heven B))) := by
  classical
  have hpositive (B : π.parts) :
      0 < (B : Finset (Fin (2 * K))).card / 2 := by
    have hp : 0 < (B : Finset (Fin (2 * K))).card :=
      Finset.card_pos.mpr (π.nonempty_of_mem_parts B.2)
    obtain ⟨k, hk⟩ := heven B
    omega
  have hblock (B : π.parts) :
      PowerSeries.mk (fun m : ℕ =>
        ∑ d : {d : ExternalInsertionWickDiagram Mode
            ((B : Finset (Fin (2 * K))).card / 2) m //
            d.vertexGraph.Preconnected},
          if d.1.externalLabel =
              evenExternalSubsetLabels labels (B : Finset (Fin (2 * K))) (heven B)
          then d.1.dysonAmplitude ε β g
            (evenExternalSubsetTimes times (B : Finset (Fin (2 * K))) (heven B))
          else 0) =
        connectedExternalInsertionDysonSeries ε β g
          (evenExternalSubsetLabels labels (B : Finset (Fin (2 * K))) (heven B))
          (evenExternalSubsetTimes times (B : Finset (Fin (2 * K))) (heven B)) := by
    apply PowerSeries.ext
    intro m
    simpa only [connectedExternalInsertionDysonSeries, PowerSeries.coeff_mk] using
      (sum_preconnectedDyson_eq_connectedCoefficient
        (n := m) (hpositive B) ε β g
        (evenExternalSubsetLabels labels (B : Finset (Fin (2 * K))) (heven B))
        (evenExternalSubsetTimes times (B : Finset (Fin (2 * K))) (heven B)))
  calc
    _ = externalPartitionSourceSign π *
          PowerSeries.coeff n
            (∏ B : π.parts,
              PowerSeries.mk (fun m : ℕ =>
                ∑ d : {d : ExternalInsertionWickDiagram Mode
                    ((B : Finset (Fin (2 * K))).card / 2) m //
                    d.vertexGraph.Preconnected},
                  if d.1.externalLabel =
                      evenExternalSubsetLabels labels (B : Finset (Fin (2 * K))) (heven B)
                  then d.1.dysonAmplitude ε β g
                    (evenExternalSubsetTimes times (B : Finset (Fin (2 * K))) (heven B))
                  else 0)) :=
      sum_fixedExternalPartitionDysonFiber_eq_signedCoeffPreconnectedSeries
        anchor π heven ε β hβ g labels times
    _ = _ := by
      apply congrArg (fun z : ℂ => externalPartitionSourceSign π * z)
      apply congrArg (PowerSeries.coeff n)
      apply Finset.prod_congr rfl
      intro B _
      exact hblock B

set_option maxHeartbeats 4000000 in
-- The even-partition sum contains dependent blockwise connected series.
open Classical in
/-- The full genuine vacuum-free physical Dyson coefficient is the sum
over even external-component partitions of Koszul-signed coefficients
of products of physically connected external-block Dyson series. -/
theorem vacuumFreeExternalInsertionDysonCoefficient_eq_sum_evenPartitionConnectedSeries
    {K n : ℕ} (anchor : Fin (2 * K))
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * K) → ExternalFieldLabel Mode)
    (times : Fin (2 * K) → ℝ) :
    vacuumFreeExternalInsertionDysonCoefficient ε β g labels times n =
      ∑ π : Finpartition (Finset.univ : Finset (Fin (2 * K))),
        if heven : ∀ B : π.parts, Even (B : Finset (Fin (2 * K))).card then
          externalPartitionSourceSign π *
            PowerSeries.coeff n
              (∏ B : π.parts,
                connectedExternalInsertionDysonSeries ε β g
                  (evenExternalSubsetLabels labels (B : Finset (Fin (2 * K))) (heven B))
                  (evenExternalSubsetTimes times (B : Finset (Fin (2 * K))) (heven B)))
        else 0 := by
  classical
  rw [vacuumFreeExternalInsertionDysonCoefficient_eq_sum_evenPartitionFibers]
  apply Finset.sum_congr rfl
  intro π _
  split_ifs with heven
  · exact sum_fixedExternalPartitionDysonFiber_eq_signedCoeffConnectedSeries
      anchor π heven ε β hβ g labels times
  · rfl

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

set_option maxHeartbeats 4000000 in
-- The finite partition sum and dependent connected-block series elaborate at each coefficient.
open Classical in
/-- The physical vacuum-free Dyson series is the finite Koszul-signed
external-partition sum of products of connected Dyson series in
`PowerSeries ℂ`. The equality preserves canonical source order and
the physical Dyson coefficients. -/
theorem vacuumFreeExternalInsertionDysonSeries_eq_sum_evenPartitionConnectedSeries
    {K : ℕ} (anchor : Fin (2 * K))
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * K) → ExternalFieldLabel Mode)
    (times : Fin (2 * K) → ℝ) :
    vacuumFreeExternalInsertionDysonSeries ε β g labels times =
      ∑ π : Finpartition (Finset.univ : Finset (Fin (2 * K))),
        if heven : ∀ B : π.parts, Even (B : Finset (Fin (2 * K))).card then
          PowerSeries.C (externalPartitionSourceSign π) *
            ∏ B : π.parts,
              connectedExternalInsertionDysonSeries ε β g
                (evenExternalSubsetLabels labels (B : Finset (Fin (2 * K))) (heven B))
                (evenExternalSubsetTimes times (B : Finset (Fin (2 * K))) (heven B))
        else 0 := by
  classical
  apply PowerSeries.ext
  intro n
  simp only [vacuumFreeExternalInsertionDysonSeries, PowerSeries.coeff_mk]
  rw [vacuumFreeExternalInsertionDysonCoefficient_eq_sum_evenPartitionConnectedSeries
    anchor ε β hβ g labels times]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro π _
  split_ifs with heven
  · simp only [PowerSeries.coeff_C_mul]
  · simp

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

/-- Transport a partition of the canonically renumbered external slots
back to its actual finite ambient source subset. The construction
preserves whole blocks rather than merely their cardinalities. -/
private noncomputable def externalSubsetReindexPartition
    (S : Finset (Fin (2 * E))) (heven : Even S.card)
    (π : Finpartition (Finset.univ : Finset (Fin (2 * (S.card / 2))))) :
    Finpartition S := by
  classical
  let e := evenExternalSubsetOrderIso S heven
  let emb : Fin (2 * (S.card / 2)) ↪ Fin (2 * E) :=
    ⟨fun i => (e i).1, fun i j hij => e.injective (Subtype.ext hij)⟩
  let part : Finset (Fin (2 * (S.card / 2))) → Finset (Fin (2 * E)) :=
    fun B => B.map emb
  refine Finpartition.ofExistsUnique (π.parts.image part) ?_ ?_ ?_
  · intro T hT
    obtain ⟨B, _, rfl⟩ := Finset.mem_image.mp hT
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    exact (e i).2
  · intro x hx
    let i := e.symm ⟨x, hx⟩
    have hi : (e i).1 = x := by simp [i]
    obtain ⟨B, hB, hiB⟩ := π.exists_mem (Finset.mem_univ i)
    refine ⟨part B, ⟨Finset.mem_image.mpr ⟨B, hB, rfl⟩, ?_⟩, ?_⟩
    · exact Finset.mem_map.mpr ⟨i, hiB, hi⟩
    intro T ⟨hT, hxT⟩
    obtain ⟨C, hC, hCT⟩ := Finset.mem_image.mp hT
    have hiC : i ∈ C := by
      rw [← hCT] at hxT
      obtain ⟨j, hjC, hjx⟩ := Finset.mem_map.mp hxT
      have hji : j = i :=
        e.injective (Subtype.ext (hjx.trans hi.symm))
      simpa [hji] using hjC
    calc
      T = part C := hCT.symm
      _ = part B := congrArg part (π.eq_of_mem_parts hC hB hiC hiB)
  · intro hEmpty
    obtain ⟨B, hB, hBEmpty⟩ := Finset.mem_image.mp hEmpty
    obtain ⟨i, hiB⟩ := π.nonempty_of_mem_parts hB
    have hi : (e i).1 ∈ part B := Finset.mem_map.mpr ⟨i, hiB, rfl⟩
    rw [hBEmpty] at hi
    simpa using hi

/-- Pull a partition of the actual source subset back to canonical
local source-slot coordinates using the same increasing order isomorphism. -/
private noncomputable def externalSubsetLocalPartition
    (S : Finset (Fin (2 * E))) (heven : Even S.card)
    (σ : Finpartition S) :
    Finpartition (Finset.univ : Finset (Fin (2 * (S.card / 2)))) := by
  classical
  let e := evenExternalSubsetOrderIso S heven
  let preimage : Finset (Fin (2 * E)) → Finset (Fin (2 * (S.card / 2))) :=
    fun T => Finset.univ.filter (fun i => (e i).1 ∈ T)
  refine Finpartition.ofExistsUnique (σ.parts.image preimage) ?_ ?_ ?_
  · intro T _ i _
    exact Finset.mem_univ i
  · intro i _
    obtain ⟨T, hT, hiT⟩ := σ.exists_mem (e i).2
    refine ⟨preimage T, ⟨Finset.mem_image.mpr ⟨T, hT, rfl⟩, ?_⟩, ?_⟩
    · simp [preimage, hiT]
    intro U ⟨hU, hiU⟩
    obtain ⟨V, hV, hVU⟩ := Finset.mem_image.mp hU
    have hiV : (e i).1 ∈ V := by
      rw [← hVU] at hiU
      exact (Finset.mem_filter.mp hiU).2
    calc
      U = preimage V := hVU.symm
      _ = preimage T := congrArg preimage (σ.eq_of_mem_parts hV hT hiV hiT)
  · intro hEmpty
    obtain ⟨T, hT, hTEmpty⟩ := Finset.mem_image.mp hEmpty
    obtain ⟨x, hxT⟩ := σ.nonempty_of_mem_parts hT
    have hxS : x ∈ S := σ.le hT hxT
    let i := e.symm ⟨x, hxS⟩
    have hiT : i ∈ preimage T := by simp [preimage, i, hxT]
    rw [hTEmpty] at hiT
    simpa using hiT

/-- Reindexing external-source partitions along the canonical increasing
order isomorphism is a genuine equivalence, not a mere relabeling of
the number of blocks. Its two directions preserve all source supports. -/
private noncomputable def externalSubsetPartitionEquiv
    (S : Finset (Fin (2 * E))) (heven : Even S.card) :
    Finpartition (Finset.univ : Finset (Fin (2 * (S.card / 2)))) ≃
      Finpartition S := by
  classical
  let e := evenExternalSubsetOrderIso S heven
  let emb : Fin (2 * (S.card / 2)) ↪ Fin (2 * E) :=
    ⟨fun i => (e i).1, fun i j hij => e.injective (Subtype.ext hij)⟩
  let f : Finset (Fin (2 * (S.card / 2))) → Finset (Fin (2 * E)) :=
    fun B => B.map emb
  let g : Finset (Fin (2 * E)) → Finset (Fin (2 * (S.card / 2))) :=
    fun T => Finset.univ.filter (fun i => (e i).1 ∈ T)
  have hgf (B : Finset (Fin (2 * (S.card / 2)))) :
      g (f B) = B := by
    ext i
    constructor
    · intro hi
      obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp (Finset.mem_filter.mp hi).2
      have h : j = i := emb.injective hji
      simpa [h] using hj
    · intro hi
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, Finset.mem_map.mpr ⟨i, hi, rfl⟩⟩
  have hfg (T : Finset (Fin (2 * E))) (hT : T ⊆ S) :
      f (g T) = T := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, hix⟩ := Finset.mem_map.mp hx
      have hmem : (e i).1 ∈ T := (Finset.mem_filter.mp hi).2
      exact hix ▸ hmem
    · intro hx
      let i := e.symm ⟨x, hT hx⟩
      apply Finset.mem_map.mpr
      refine ⟨i, ?_, ?_⟩
      · simp [g, i, hx]
      · change (e (e.symm ⟨x, hT hx⟩)).1 = x
        simp
  refine
    { toFun := externalSubsetReindexPartition S heven
      invFun := externalSubsetLocalPartition S heven
      left_inv := ?_
      right_inv := ?_ }
  · intro π
    apply Finpartition.ext
    change (π.parts.image f).image g = π.parts
    ext B
    constructor
    · intro hB
      obtain ⟨T, hT, hTB⟩ := Finset.mem_image.mp hB
      obtain ⟨C, hC, hCT⟩ := Finset.mem_image.mp hT
      have hBC : B = C := by
        calc
          B = g T := hTB.symm
          _ = g (f C) := congrArg g hCT.symm
          _ = C := hgf C
      simpa [hBC] using hC
    · intro hB
      exact Finset.mem_image.mpr
        ⟨f B, Finset.mem_image.mpr ⟨B, hB, rfl⟩, hgf B⟩
  · intro σ
    apply Finpartition.ext
    change (σ.parts.image g).image f = σ.parts
    ext T
    constructor
    · intro hT
      obtain ⟨B, hB, hBT⟩ := Finset.mem_image.mp hT
      obtain ⟨C, hC, hCB⟩ := Finset.mem_image.mp hB
      have hTC : T = C := by
        calc
          T = f B := hBT.symm
          _ = f (g C) := congrArg f hCB.symm
          _ = C := hfg C (σ.le hC)
      simpa [hTC] using hC
    · intro hT
      exact Finset.mem_image.mpr
        ⟨g T, Finset.mem_image.mpr ⟨T, hT, rfl⟩, hfg T (σ.le hT)⟩

/-- Corresponding blocks under the source-subset partition
equivalence. It is the restriction of the partition equivalence to
the actual finite block families, so finite products reindex
without introducing a block multiplicity. -/
private noncomputable def externalSubsetPartsEquiv
    (S : Finset (Fin (2 * E))) (heven : Even S.card)
    (π : Finpartition (Finset.univ : Finset (Fin (2 * (S.card / 2))))) :
    π.parts ≃ (externalSubsetPartitionEquiv S heven π).parts := by
  classical
  let e := evenExternalSubsetOrderIso S heven
  let emb : Fin (2 * (S.card / 2)) ↪ Fin (2 * E) :=
    ⟨fun i => (e i).1, fun i j hij => e.injective (Subtype.ext hij)⟩
  let σ := externalSubsetPartitionEquiv S heven π
  have hparts : σ.parts =
      π.parts.image (fun B => B.map emb) := rfl
  let f : π.parts → σ.parts := fun B =>
    ⟨B.1.map emb, by
      rw [hparts]
      exact Finset.mem_image.mpr ⟨B.1, B.2, rfl⟩⟩
  have hf : Function.Injective f := by
    intro B C hBC
    apply Subtype.ext
    exact (Finset.map_injective emb) (congrArg Subtype.val hBC)
  have hg : Function.Surjective f := by
    intro T
    have hT : T.1 ∈ π.parts.image (fun B => B.map emb) := by
      rw [← hparts]
      exact T.2
    obtain ⟨B, hB, hBT⟩ := Finset.mem_image.mp hT
    exact ⟨⟨B, hB⟩, Subtype.ext hBT⟩
  exact Equiv.ofBijective f ⟨hf, hg⟩

/-- In the increasing-order partition shuffle of a source subset,
the ambient shuffle positions occupied by a block are exactly the
positions whose source labels belong to that block. This is the
subset counterpart of `shuffleOfIncreasingOrderFull_blockSlotSet`. -/
private theorem externalSubsetShuffle_blockSlotSet
    (S : Finset (Fin (2 * E)))
    (σ : Finpartition S) (B : σ.parts) :
    σ.shuffleOfIncreasingOrder.blockSlotSet B =
      Finset.univ.filter (fun i : Fin S.card =>
        ((S.orderIsoOfFin rfl) i).1 ∈ (B : Finset (Fin (2 * E)))) := by
  classical
  let o : Fin S.card ≃ ↥S := (S.orderIsoOfFin rfl).toEquiv
  let orders := σ.partOrdersOfOrder o
  have hslot (j : Fin (B : Finset (Fin (2 * E))).card) :
      σ.shuffleOfIncreasingOrder.slotEquiv ⟨B, j⟩ =
        o.symm (σ.equivSigmaParts.symm ⟨B, orders B j⟩) := by
    rfl
  ext i
  simp only [Combinatorics.FamilySlotShuffleTo.blockSlotSet, Finset.mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    rw [← hj, hslot]
    change (o (o.symm (σ.equivSigmaParts.symm ⟨B, orders B j⟩))).1 ∈
      (B : Finset (Fin (2 * E)))
    simpa [Finpartition.equivSigmaParts] using (orders B j).2
  · intro hi
    let t : ↥(B : Finset (Fin (2 * E))) :=
      ⟨((S.orderIsoOfFin rfl) i).1, hi⟩
    let j := (orders B).symm t
    refine ⟨j, ?_⟩
    rw [hslot]
    have ht : σ.equivSigmaParts.symm ⟨B, orders B j⟩ = o i := by
      apply Subtype.ext
      change (orders B j).1 = (o i).1
      simp [j, t, o]
    rw [ht]
    exact o.symm_apply_apply i

/-- The inversion count of the canonical shuffle of a partition
of a subset is the number of cross-block inversions of the *actual
ambient labels*. The canonical source-order map is increasing, so
the result does not depend on gaps in the source subset. -/
private theorem externalSubsetShuffle_blockInversionCount
    (S : Finset (Fin (2 * E)))
    (σ : Finpartition S) (C D : σ.parts) (hCD : C ≠ D) :
    σ.shuffleOfIncreasingOrder.blockInversionCount C D =
      ∑ x ∈ (C : Finset (Fin (2 * E))),
        ∑ y ∈ (D : Finset (Fin (2 * E))),
          if y < x then (1 : ℕ) else 0 := by
  classical
  let o := S.orderIsoOfFin rfl
  let emb : Fin S.card ↪ Fin (2 * E) :=
    ⟨fun i => (o i).1, fun i j h => o.injective (Subtype.ext h)⟩
  let idx (T : Finset (Fin (2 * E))) : Finset (Fin S.card) :=
    Finset.univ.filter (fun i => emb i ∈ T)
  have hmem (T : σ.parts) :
      (idx T.1).map emb = (T : Finset (Fin (2 * E))) := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, hix⟩ := Finset.mem_map.mp hx
      exact hix ▸ (Finset.mem_filter.mp hi).2
    · intro hx
      let i := o.symm ⟨x, σ.le T.2 hx⟩
      apply Finset.mem_map.mpr
      refine ⟨i, ?_, ?_⟩
      · have hiEq : emb i = x := by
          change (o (o.symm ⟨x, σ.le T.2 hx⟩)).1 = x
          simp
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiEq ▸ hx⟩
      · change (o (o.symm ⟨x, σ.le T.2 hx⟩)).1 = x
        simp
  have horder (i j : Fin S.card) :
      (emb j < emb i) ↔ j < i := by
    change (o j).1 < (o i).1 ↔ j < i
    exact o.lt_iff_lt
  rw [σ.shuffleOfIncreasingOrder.blockInversionCount_eq_sum_blockSlotSet hCD,
    externalSubsetShuffle_blockSlotSet S σ C,
    externalSubsetShuffle_blockSlotSet S σ D]
  change (∑ x ∈ idx C.1, ∑ y ∈ idx D.1, if y < x then 1 else 0) = _
  calc
    _ = ∑ x ∈ idx C.1, ∑ y ∈ idx D.1,
          if emb y < emb x then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      simp only [horder]
    _ = ∑ x ∈ (idx C.1).map emb,
          ∑ y ∈ (idx D.1).map emb, if y < x then 1 else 0 := by
      simp only [Finset.sum_map]
    _ = _ := by rw [hmem C, hmem D]

/-- A source partition has only even-sized blocks if and only if its
image under the canonical order-preserving reindexing does. This permits
restricting both signed connected-partition sums to the same physical
even-block sector, without changing block multiplicities. -/
private theorem externalSubsetPartitionEquiv_evenBlocks
    (S : Finset (Fin (2 * E))) (heven : Even S.card)
    (π : Finpartition (Finset.univ : Finset (Fin (2 * (S.card / 2))))) :
    (∀ B : π.parts, Even (B : Finset (Fin (2 * (S.card / 2)))).card) ↔
      ∀ T : (externalSubsetPartitionEquiv S heven π).parts,
        Even (T : Finset (Fin (2 * E))).card := by
  classical
  let e := evenExternalSubsetOrderIso S heven
  let emb : Fin (2 * (S.card / 2)) ↪ Fin (2 * E) :=
    ⟨fun i => (e i).1, fun i j hij => e.injective (Subtype.ext hij)⟩
  let be := externalSubsetPartsEquiv S heven π
  have hcard (B : π.parts) : (be B).1.card = B.1.card := by
    change (B.1.map emb).card = B.1.card
    simp
  constructor
  · intro hEven T
    obtain ⟨B, rfl⟩ := be.surjective T
    simpa only [hcard B] using hEven B
  · intro hEven B
    simpa only [hcard B] using hEven (be B)

set_option maxHeartbeats 4000000 in
-- Relabelled blocks have dependent local sizes, so compare their inversion counts via ambient sets.
open Classical in
/-- The canonical fermionic source sign is unchanged when the
canonically increasing local external slots of an even source subset
are relabelled by their actual ambient source positions. The
even-block condition removes any dependence on arbitrary block order. -/
private theorem externalSubsetPartitionEquiv_sourceSign
    (S : Finset (Fin (2 * E))) (heven : Even S.card)
    (π : Finpartition (Finset.univ : Finset (Fin (2 * (S.card / 2)))))
    (hEven : ∀ B : π.parts, Even (B : Finset (Fin (2 * (S.card / 2)))).card) :
    externalPartitionSourceSign π =
      externalPartitionSourceSign (externalSubsetPartitionEquiv S heven π) := by
  classical
  let σ := externalSubsetPartitionEquiv S heven π
  let e := evenExternalSubsetOrderIso S heven
  let emb : Fin (2 * (S.card / 2)) ↪ Fin (2 * E) :=
    ⟨fun i => (e i).1, fun i j hij => e.injective (Subtype.ext hij)⟩
  let be : π.parts ≃ σ.parts := externalSubsetPartsEquiv S heven π
  let hc : Fintype.card π.parts = Fintype.card σ.parts := Fintype.card_congr be
  let orderπ : π.parts ≃ Fin (Fintype.card π.parts) := Fintype.equivFin _
  let orderσ : σ.parts ≃ Fin (Fintype.card σ.parts) :=
    (be.symm.trans orderπ).trans (finCongr hc)
  have horder (B C : π.parts) :
      orderπ B < orderπ C ↔ orderσ (be B) < orderσ (be C) := by
    simp [orderσ, Fin.cast_lt_cast]
  have hsource (B C : π.parts) (hBC : B ≠ C) :
      π.shuffleOfIncreasingOrder.blockInversionCount B C =
        ∑ x ∈ (B : Finset (Fin (2 * (S.card / 2)))),
          ∑ y ∈ (C : Finset (Fin (2 * (S.card / 2)))),
            if y < x then (1 : ℕ) else 0 := by
    calc
      _ = (externalPartitionShuffleFull π).blockInversionCount B C :=
        ((π.shuffleOfIncreasingOrder).castTotalEquiv_blockInversionCount (by simp) B C).symm
      _ = _ := by
        rw [(externalPartitionShuffleFull π).blockInversionCount_eq_sum_blockSlotSet hBC]
        change
          (∑ x ∈ ((Combinatorics.FamilySlotShuffleTo.castTotalEquiv (by simp))
              π.shuffleOfIncreasingOrder).blockSlotSet B,
            ∑ y ∈ ((Combinatorics.FamilySlotShuffleTo.castTotalEquiv (by simp))
              π.shuffleOfIncreasingOrder).blockSlotSet C, if y < x then 1 else 0) = _
        rw [π.shuffleOfIncreasingOrderFull_blockSlotSet B,
          π.shuffleOfIncreasingOrderFull_blockSlotSet C]
  have hlocalOrder (i j : Fin (2 * (S.card / 2))) :
      emb i < emb j ↔ i < j := by
    change (e i).1 < (e j).1 ↔ i < j
    exact e.lt_iff_lt
  have hInv (B C : π.parts) :
      π.shuffleOfIncreasingOrder.blockInversionCount B C =
        σ.shuffleOfIncreasingOrder.blockInversionCount (be B) (be C) := by
    by_cases hBC : B = C
    · subst C
      simp only [Combinatorics.FamilySlotShuffleTo.blockInversionCount_self]
    · rw [hsource B C hBC,
        externalSubsetShuffle_blockInversionCount S σ (be B) (be C) (be.injective.ne hBC)]
      change (∑ x ∈ B.1, ∑ y ∈ C.1, if y < x then (1 : ℕ) else 0) =
        ∑ x ∈ B.1.map emb, ∑ y ∈ C.1.map emb, if y < x then 1 else 0
      simp only [Finset.sum_map, hlocalOrder]
  have hcount :
      π.shuffleOfIncreasingOrder.orderedBlockInversionCount orderπ =
        σ.shuffleOfIncreasingOrder.orderedBlockInversionCount orderσ := by
    classical
    unfold Combinatorics.FamilySlotShuffleTo.orderedBlockInversionCount
    refine Finset.sum_bij (fun p _ => (be p.1, be p.2)) ?_ ?_ ?_ ?_
    · intro p hp
      exact Finset.mem_offDiag.mpr
        ⟨Finset.mem_univ _, Finset.mem_univ _, be.injective.ne (Finset.mem_offDiag.mp hp).2.2⟩
    · intro p _ q _ hpq
      exact Prod.ext (be.injective (congrArg Prod.fst hpq))
        (be.injective (congrArg Prod.snd hpq))
    · intro q hq
      refine ⟨(be.symm q.1, be.symm q.2), ?_, ?_⟩
      · exact Finset.mem_offDiag.mpr
          ⟨Finset.mem_univ _, Finset.mem_univ _, by
            intro h
            apply (Finset.mem_offDiag.mp hq).2.2
            simpa using congrArg be h⟩
      · ext <;> simp
    · intro p _
      by_cases hp : orderπ p.1 < orderπ p.2
      · have hq : orderσ (be p.1) < orderσ (be p.2) := (horder p.1 p.2).mp hp
        simp only [hp, hq, ite_true]
        exact hInv p.1 p.2
      · have hq : ¬ orderσ (be p.1) < orderσ (be p.2) :=
          fun h => hp ((horder p.1 p.2).mpr h)
        simp [hp, hq]
  calc
    externalPartitionSourceSign π = externalPartitionOrderSign π orderπ := rfl
    _ = externalPartitionOrderSign σ orderσ := by
      unfold externalPartitionOrderSign
      exact congrArg (fun k : ℕ => (Common.Statistics.fermion.zetaInt : ℂ) ^ k)
        hcount
    _ = externalPartitionSourceSign σ :=
      externalPartitionOrderSign_eq_of_blockOrder σ
        ((externalSubsetPartitionEquiv_evenBlocks S heven π).mp hEven)
        orderσ (Fintype.equivFin _)

/-- An increasing source-slot enumeration restricted to an
increasing subfamily agrees with the canonical enumeration of
the corresponding ambient image. -/
private theorem externalSubsetOrderEmb_image
    {n m k : ℕ} (S : Finset (Fin n)) (hS : S.card = m)
    (B : Finset (Fin m)) (hB : B.card = k) (i : Fin k) :
    (S.orderEmbOfFin hS) (B.orderEmbOfFin hB i) =
      ((B.map (S.orderEmbOfFin hS).toEmbedding).orderEmbOfFin
        (by simp [hB])) i := by
  classical
  let e := S.orderEmbOfFin hS
  let T := B.map e.toEmbedding
  have hcard : T.card = k := by simp [T, hB]
  have hmem (j : Fin k) : e (B.orderEmbOfFin hB j) ∈ T := by
    exact Finset.mem_map.mpr
      ⟨B.orderEmbOfFin hB j, Finset.orderEmbOfFin_mem B hB j, rfl⟩
  have hmono : StrictMono (fun j : Fin k => e (B.orderEmbOfFin hB j)) :=
    e.strictMono.comp (B.orderEmbOfFin hB).strictMono
  have hu := Finset.orderEmbOfFin_unique hcard hmem hmono
  exact congrFun hu i

/-- Restricting the increasing source order to a connected
subblock agrees with the increasing enumeration of that block in the
original ambient source coordinates. This is the order-level
compatibility needed for both labels and insertion times. -/
private theorem externalSubsetOrderIso_comp
    (S : Finset (Fin (2 * E))) (heven : Even S.card)
    (B : Finset (Fin (2 * (S.card / 2)))) (hB : Even B.card)
    (hT : Even (B.map
      (S.orderEmbOfFin (Nat.two_mul_div_two_of_even heven).symm).toEmbedding).card)
    (i : Fin (2 * (B.card / 2))) :
    ((evenExternalSubsetOrderIso S heven)
      ((evenExternalSubsetOrderIso B hB i).1)).1 =
    ((evenExternalSubsetOrderIso
        (B.map (S.orderEmbOfFin
          (Nat.two_mul_div_two_of_even heven).symm).toEmbedding) hT)
        (Fin.cast (by simp) i)).1 := by
  classical
  let hcardS : S.card = 2 * (S.card / 2) :=
    (Nat.two_mul_div_two_of_even heven).symm
  let emb := (S.orderEmbOfFin hcardS).toEmbedding
  let T := B.map emb
  have hcardB : B.card = 2 * (B.card / 2) :=
    (Nat.two_mul_div_two_of_even hB).symm
  have hcardT : T.card = 2 * (B.card / 2) := by simpa [T] using hcardB
  have hsize : 2 * (B.card / 2) = 2 * (T.card / 2) := by simp [T]
  have hg := externalSubsetOrderEmb_image S hcardS B hcardB i
  have hcanon : T.orderIsoOfFin hcardT =
      (Fin.castOrderIso hsize).trans (evenExternalSubsetOrderIso T hT) :=
    Subsingleton.elim _ _
  have ht : (T.orderEmbOfFin hcardT) i =
      ((evenExternalSubsetOrderIso T hT) (Fin.cast hsize i)).1 := by
    exact congrArg
      (fun iso : Fin (2 * (B.card / 2)) ≃o ↥T => (iso i).1) hcanon
  calc
    _ = (T.orderEmbOfFin hcardT) i := hg
    _ = _ := ht

/-- Transport nested canonical order enumerations to any provably
equal ambient block, rather than relying on definitional equality of
the two finite-set image implementations. -/
private theorem externalSubsetOrderIso_comp_of_eq
    (S : Finset (Fin (2 * E))) (heven : Even S.card)
    (B : Finset (Fin (2 * (S.card / 2)))) (hB : Even B.card)
    (T : Finset (Fin (2 * E))) (hT : Even T.card)
    (hT_eq : T = B.map
      (S.orderEmbOfFin (Nat.two_mul_div_two_of_even heven).symm).toEmbedding)
    (i : Fin (2 * (B.card / 2))) :
    ((evenExternalSubsetOrderIso S heven)
      ((evenExternalSubsetOrderIso B hB i).1)).1 =
    ((evenExternalSubsetOrderIso T hT)
      (Fin.cast (by simp [hT_eq]) i)).1 := by
  subst T
  exact externalSubsetOrderIso_comp S heven B hB hT i

set_option maxHeartbeats 4000000 in
-- The connected series of a source subset has an index depending on its cardinality.
open Classical in
/-- The physical moment of any nonempty even external source subset has
an explicit signed connected-partition expansion on its *canonically
renumbered* external slots. Block signs and amplitudes use the
canonical increasing source-subset order. -/
theorem externalSubsetMomentSeries_eq_signedConnectedSum_localIndices
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (times : Fin (2 * E) → ℝ)
    (S : Finset (Fin (2 * E))) (hS : S ≠ ∅) (heven : Even S.card) :
    externalSubsetMomentSeries ε β g labels times S =
      ∑ π : Finpartition
          (Finset.univ : Finset (Fin (2 * (S.card / 2)))),
        if hevenBlocks : ∀ B : π.parts,
            Even (B : Finset (Fin (2 * (S.card / 2)))).card then
          PowerSeries.C (externalPartitionSourceSign π) *
            ∏ B : π.parts,
              connectedExternalInsertionDysonSeries ε β g
                (evenExternalSubsetLabels
                  (evenExternalSubsetLabels labels S heven)
                  (B : Finset (Fin (2 * (S.card / 2)))) (hevenBlocks B))
                (evenExternalSubsetTimes
                  (evenExternalSubsetTimes times S heven)
                  (B : Finset (Fin (2 * (S.card / 2)))) (hevenBlocks B))
        else 0 := by
  classical
  have hpositive : 0 < 2 * (S.card / 2) := by
    have hsCard : 0 < S.card :=
      Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
    obtain ⟨k, hk⟩ := heven
    omega
  have hfull := vacuumFreeExternalInsertionDysonSeries_eq_sum_evenPartitionConnectedSeries
    (anchor := (⟨0, hpositive⟩ : Fin (2 * (S.card / 2))))
    ε β hβ g (evenExternalSubsetLabels labels S heven)
      (evenExternalSubsetTimes times S heven)
  simpa [externalSubsetMomentSeries, hS, heven] using hfull

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

/-- A pair of functions on finite slot families with equal
cardinalities can be compared heterogeneously without eliminating
dependent equations between fixed expressions. -/
private theorem externalSubsetFunctions_heq_of_cast
    {α : Type*} {n m : ℕ} (h : n = m)
    (f : Fin (2 * n) → α) (g : Fin (2 * m) → α)
    (hfg : ∀ i, f i = g (Fin.cast (congrArg (2 * ·) h) i)) :
    HEq f g := by
  cases h
  apply heq_of_eq
  funext i
  simpa using hfg i

/-- A connected Dyson series is unchanged by heterogeneous equality
of the ordered external fields and insertion times across equal pair counts. -/
private theorem connectedExternalInsertionDysonSeries_heq_of_fields
    {K L : ℕ} (hKL : K = L)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labelsK : Fin (2 * K) → ExternalFieldLabel Mode)
    (labelsL : Fin (2 * L) → ExternalFieldLabel Mode)
    (timesK : Fin (2 * K) → ℝ)
    (timesL : Fin (2 * L) → ℝ)
    (hLabels : HEq labelsK labelsL)
    (hTimes : HEq timesK timesL) :
    HEq (connectedExternalInsertionDysonSeries ε β g labelsK timesK)
      (connectedExternalInsertionDysonSeries ε β g labelsL timesL) := by
  cases hKL
  have hL : labelsK = labelsL := eq_of_heq hLabels
  have hT : timesK = timesL := eq_of_heq hTimes
  cases hL
  cases hT
  rfl

set_option maxHeartbeats 4000000 in
-- Source-subset local labels and times have cardinality-dependent index types.
open Classical in
/-- The physical fully connected Dyson series of a locally numbered
external block agrees with the connected series of that block in the
original ambient source coordinates. This is a genuine equality of
external fields and times, not a permutation-invariance assumption
about individual Dyson integrals. -/
private theorem externalSubsetConnectedSeries_comp
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (times : Fin (2 * E) → ℝ)
    (S : Finset (Fin (2 * E))) (heven : Even S.card)
    (π : Finpartition (Finset.univ : Finset (Fin (2 * (S.card / 2)))))
    (hEven : ∀ B : π.parts, Even (B : Finset (Fin (2 * (S.card / 2)))).card)
    (B : π.parts) :
    connectedExternalInsertionDysonSeries ε β g
        (evenExternalSubsetLabels
          (evenExternalSubsetLabels labels S heven) B.1 (hEven B))
        (evenExternalSubsetTimes
          (evenExternalSubsetTimes times S heven) B.1 (hEven B)) =
      externalSubsetConnectedDiagramSeries ε β g labels times
        ((externalSubsetPartsEquiv S heven π B).1) := by
  classical
  let σ := externalSubsetPartitionEquiv S heven π
  let be := externalSubsetPartsEquiv S heven π
  let e := evenExternalSubsetOrderIso S heven
  let emb : Fin (2 * (S.card / 2)) ↪ Fin (2 * E) :=
    ⟨fun i => (e i).1, fun i j hij => e.injective (Subtype.ext hij)⟩
  have hImage : (be B).1 = B.1.map emb := rfl
  have hImageOrder :
      B.1.map (S.orderEmbOfFin
        ((Nat.two_mul_div_two_of_even heven).symm)).toEmbedding =
          (be B).1 := by
    calc
      _ = B.1.map emb := rfl
      _ = (be B).1 := hImage.symm
  have hEvenT : Even ((be B).1).card :=
    (externalSubsetPartitionEquiv_evenBlocks S heven π).mp hEven (be B)
  have hNotEmpty : (be B).1 ≠ ∅ := σ.ne_empty (be B).2
  have hTarget :
      externalSubsetConnectedDiagramSeries ε β g labels times (be B).1 =
        connectedExternalInsertionDysonSeries ε β g
          (evenExternalSubsetLabels labels (be B).1 hEvenT)
          (evenExternalSubsetTimes times (be B).1 hEvenT) := by
    simp [externalSubsetConnectedDiagramSeries, hNotEmpty, hEvenT]
  rw [hTarget]
  have hK : B.1.card / 2 = ((be B).1).card / 2 := by
    simp [hImage]
  have hLabels : HEq
      (evenExternalSubsetLabels
        (evenExternalSubsetLabels labels S heven) B.1 (hEven B))
      (evenExternalSubsetLabels labels (be B).1 hEvenT) := by
    apply externalSubsetFunctions_heq_of_cast hK
    intro i
    simpa only [evenExternalSubsetLabels] using
      congrArg labels
        (externalSubsetOrderIso_comp_of_eq S heven B.1 (hEven B)
          (be B).1 hEvenT hImageOrder.symm i)
  have hTimes : HEq
      (evenExternalSubsetTimes
        (evenExternalSubsetTimes times S heven) B.1 (hEven B))
      (evenExternalSubsetTimes times (be B).1 hEvenT) := by
    apply externalSubsetFunctions_heq_of_cast hK
    intro i
    simpa only [evenExternalSubsetTimes] using
      congrArg times
        (externalSubsetOrderIso_comp_of_eq S heven B.1 (hEven B)
          (be B).1 hEvenT hImageOrder.symm i)
  have hSeries : HEq
      (connectedExternalInsertionDysonSeries ε β g
        (evenExternalSubsetLabels
          (evenExternalSubsetLabels labels S heven) B.1 (hEven B))
        (evenExternalSubsetTimes
          (evenExternalSubsetTimes times S heven) B.1 (hEven B)))
      (connectedExternalInsertionDysonSeries ε β g
        (evenExternalSubsetLabels labels (be B).1 hEvenT)
        (evenExternalSubsetTimes times (be B).1 hEvenT)) :=
    connectedExternalInsertionDysonSeries_heq_of_fields
      hK ε β g _ _ _ _ hLabels hTimes
  exact eq_of_heq hSeries

/-- The Koszul-signed external-partition moment transform of fully
connected physical Dyson diagram contributions. -/
noncomputable def externalSubsetSignedConnectedMomentSeries
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (times : Fin (2 * E) → ℝ)
    (S : Finset (Fin (2 * E))) : PowerSeries ℂ :=
  Finpartition.weightedMomentFromCumulant
    (fun _ π => PowerSeries.C (externalPartitionSourceSign π))
    (externalSubsetConnectedDiagramSeries ε β g labels times) S

set_option maxHeartbeats 4000000 in
-- The outer partition and its blockwise connected products reindex dependently.
open Classical in
/-- For every nonempty even external source subset, the physical
vacuum-free Dyson moment equals the Koszul-signed partition transform
of fully connected diagram series. -/
theorem externalSubsetMomentSeries_eq_signedConnected_nonempty_even
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (times : Fin (2 * E) → ℝ)
    (S : Finset (Fin (2 * E))) (hS : S ≠ ∅) (heven : Even S.card) :
    externalSubsetMomentSeries ε β g labels times S =
      externalSubsetSignedConnectedMomentSeries ε β g labels times S := by
  classical
  rw [externalSubsetMomentSeries_eq_signedConnectedSum_localIndices
    ε β hβ g labels times S hS heven]
  unfold externalSubsetSignedConnectedMomentSeries Finpartition.weightedMomentFromCumulant
  rw [← Equiv.sum_comp (externalSubsetPartitionEquiv S heven)]
  apply Finset.sum_congr rfl
  intro π _
  let σ := externalSubsetPartitionEquiv S heven π
  let be := externalSubsetPartsEquiv S heven π
  let κ := externalSubsetConnectedDiagramSeries ε β g labels times
  by_cases hEven : ∀ B : π.parts,
      Even (B : Finset (Fin (2 * (S.card / 2)))).card
  · have hsign := externalSubsetPartitionEquiv_sourceSign S heven π hEven
    have hprod :
        (∏ B : π.parts,
            connectedExternalInsertionDysonSeries ε β g
              (evenExternalSubsetLabels
                (evenExternalSubsetLabels labels S heven) B.1 (hEven B))
              (evenExternalSubsetTimes
                (evenExternalSubsetTimes times S heven) B.1 (hEven B))) =
          Finpartition.partitionProduct κ σ := by
      calc
        _ = ∏ B : π.parts, κ (be B).1 := by
          apply Finset.prod_congr rfl
          intro B _
          exact externalSubsetConnectedSeries_comp
            ε β g labels times S heven π hEven B
        _ = ∏ T : σ.parts, κ T.1 := by
          exact Equiv.prod_comp be (fun T : σ.parts => κ T.1)
        _ = _ := by
          rw [Finpartition.partitionProduct]
          exact (Finset.prod_coe_sort σ.parts κ)
    simp only [dite_eq_left hEven]
    rw [hsign, hprod]
  · obtain ⟨B, hBodd⟩ := not_forall.mp hEven
    have hImage :
        ((be B).1 : Finset (Fin (2 * E))) =
          B.1.map
            ⟨fun i => (evenExternalSubsetOrderIso S heven i).1,
              fun i j h => (evenExternalSubsetOrderIso S heven).injective
                (Subtype.ext h)⟩ := rfl
    have hOdd : ¬ Even ((be B).1 : Finset (Fin (2 * E))).card := by
      simpa [hImage] using hBodd
    have hzero : κ (be B).1 = 0 := by
      change externalSubsetConnectedDiagramSeries ε β g labels times (be B).1 = 0
      simp [externalSubsetConnectedDiagramSeries, hOdd]
    have hprod : Finpartition.partitionProduct κ σ = 0 := by
      unfold Finpartition.partitionProduct
      exact Finset.prod_eq_zero (be B).2 hzero
    simp only [dite_eq_right hEven]
    change (0 : PowerSeries ℂ) =
      PowerSeries.C (externalPartitionSourceSign σ) * Finpartition.partitionProduct κ σ
    rw [hprod]
    simp

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
  have hne : S ≠ ∅ := fun h => hodd (by simpa [h])
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

/-- The physical signed partition identity for nonempty even external
subsets extends to all subsets by vacuum normalization for the empty
subset and fermion parity for odd subsets. -/
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
  rcases eq_or_ne S ∅ with rfl | hEmpty
  · simp
  rcases em (Even S.card) with hParity | hParity
  · exact hEven S hEmpty hParity
  · rw [(externalSubsetSeries_eq_zero_of_odd ε β g labels times S hParity).1,
      externalSubsetSignedConnectedMomentSeries_eq_zero_of_odd
        ε β g labels times S hParity]

/-- Every vacuum-normalized physical Dyson moment is the fermionic
Koszul-signed partition transform of fully connected diagram series.
Empty and odd subsets follow from normalization and fermion parity. -/
theorem externalSubsetMomentSeries_eq_signedConnected
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (times : Fin (2 * E) → ℝ) :
    ∀ S : Finset (Fin (2 * E)),
      externalSubsetMomentSeries ε β g labels times S =
        externalSubsetSignedConnectedMomentSeries ε β g labels times S := by
  apply externalSubsetMomentSeries_eq_signedConnected_of_nonempty_even
    ε β g labels times
  intro S hS heven
  exact externalSubsetMomentSeries_eq_signedConnected_nonempty_even
    ε β hβ g labels times S hS heven

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
    have hpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hEmpty)
    have hle : S.card ≤ 2 := by
      simpa using Finset.card_le_card (Finset.subset_univ S)
    obtain ⟨k, hk⟩ := hEven
    omega
  have hproper :
      ∀ B : Finset (Fin 2), B ⊂ S →
        externalSubsetConnectedDiagramSeries (E := 1) ε β g labels times B = 0 := by
    intro B hB
    have hlt := Finset.card_lt_card hB
    rcases (show B.card = 0 ∨ B.card = 1 by omega) with hzero | hone
    · simp [Finset.card_eq_zero.mp hzero, externalSubsetConnectedDiagramSeries]
    · exact (externalSubsetSeries_eq_zero_of_odd (E := 1)
        ε β g labels times B (by simp [hone])).2
  calc
    _ = externalSubsetConnectedDiagramSeries (E := 1) ε β g labels times S := by
      simp only [externalSubsetMomentSeries, externalSubsetConnectedDiagramSeries,
        hEmpty, hEven, dite_eq_left]
      exact vacuumFreeExternalInsertionDysonSeries_eq_connected_of_single_pair
        (show S.card / 2 = 1 by omega) ε β g
        (evenExternalSubsetLabels (E := 1) labels S hEven)
        (evenExternalSubsetTimes (E := 1) times S hEven)
    _ = _ :=
      (externalPartitionWeightedMoment_eq_of_proper_zero (E := 1)
        (externalSubsetConnectedDiagramSeries (E := 1) ε β g labels times)
        S hEmpty hproper).symm

/-- The source cumulant of physical vacuum-normalized Dyson moments
equals the fully externally connected diagram series for any finite
number of external insertions.

The proof applies signed moment reconstruction and injectivity to the
physical Koszul-signed partition identity. Vacuum normalization alone
does not require all external insertions to be connected. -/
theorem externalSubsetSourceCumulantSeries_eq_connectedDiagramSeries
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (times : Fin (2 * E) → ℝ) :
    externalSubsetSourceCumulantSeries
        (externalSubsetMomentSeries ε β g labels times) =
      externalSubsetConnectedDiagramSeries ε β g labels times := by
  apply externalPartitionWeightedMoment_injective
  · simp
  · intro S
    exact (externalSubsetSourceCumulantSeries_reconstruct
      (externalSubsetMomentSeries ε β g labels times) (by simp) S).trans
      (externalSubsetMomentSeries_eq_signedConnected ε β hβ g labels times S)


/-- For two external insertions, the source cumulant equals the
connected physical Dyson series without a sign restriction on β. -/
theorem externalSubsetSourceCumulantSeries_eq_connectedDiagramSeries_two
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin 2 → ExternalFieldLabel Mode)
    (times : Fin 2 → ℝ) :
    externalSubsetSourceCumulantSeries (E := 1)
        (externalSubsetMomentSeries (E := 1) ε β g labels times) =
      externalSubsetConnectedDiagramSeries (E := 1) ε β g labels times := by
  apply externalPartitionWeightedMoment_injective (E := 1)
  · simp only [externalSubsetSourceCumulantSeries_empty,
      externalSubsetConnectedDiagramSeries_empty]
  · intro S
    exact (externalSubsetSourceCumulantSeries_reconstruct (E := 1)
      (externalSubsetMomentSeries (E := 1) ε β g labels times)
      (externalSubsetMomentSeries_empty (E := 1) ε β g labels times) S).trans
      (externalSubsetMomentSeries_eq_signedConnected_two ε β g labels times S)


/-- Vacuum-normalized source moment at physical dispersion ε and chemical potential μ.
The effective-dispersion diagram series is multiplied by exactly the product of
the physical external-field factors; empty and odd subsets retain their normalization. -/
noncomputable def grandCanonicalExternalSubsetMomentSeries
    (ε : Mode → ℝ) (β μ : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (times : Fin (2 * E) → ℝ)
    (S : Finset (Fin (2 * E))) : PowerSeries ℂ :=
  (∏ i ∈ S, PowerSeries.C (externalFieldChemicalPotentialFactor μ (times i) (labels i))) *
    externalSubsetMomentSeries (fun k => ε k - μ) β g labels times S

/-- Fully connected physical-H diagrams at explicit chemical potential.
The external factors multiply the actual effective-dispersion connected diagram
sum, rather than defining connectivity through moment inversion. -/
noncomputable def grandCanonicalExternalSubsetConnectedDiagramSeries
    (ε : Mode → ℝ) (β μ : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (times : Fin (2 * E) → ℝ)
    (S : Finset (Fin (2 * E))) : PowerSeries ℂ :=
  (∏ i ∈ S, PowerSeries.C (externalFieldChemicalPotentialFactor μ (times i) (labels i))) *
    externalSubsetConnectedDiagramSeries (fun k => ε k - μ) β g labels times S

/-- The finite subset product of external factors agrees with the product in
its canonical even-slot indexing. -/
private theorem externalSubsetChemicalPotentialFactor_eq_family
    (μ : ℝ) (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (times : Fin (2 * E) → ℝ)
    (S : Finset (Fin (2 * E))) (heven : Even S.card) :
    (∏ i ∈ S, PowerSeries.C (externalFieldChemicalPotentialFactor μ (times i) (labels i))) =
      PowerSeries.C (externalFieldFamilyChemicalPotentialFactor μ
        (evenExternalSubsetLabels labels S heven)
        (evenExternalSubsetTimes times S heven)) := by
  unfold externalFieldFamilyChemicalPotentialFactor
  rw [map_prod]
  rw [← Finset.prod_coe_sort S
    (fun i => PowerSeries.C (externalFieldChemicalPotentialFactor μ (times i) (labels i)))]
  exact (Equiv.prod_comp (evenExternalSubsetOrderIso S heven).toEquiv
    (fun i : S => PowerSeries.C
      (externalFieldChemicalPotentialFactor μ (times i.1) (labels i.1)))).symm

/-- For every nonempty even subset, the explicit-μ source moment recovers the
physical-H operator Dyson series upon multiplication by the normalized grand-canonical
vacuum series. This identifies the physical normalization independently of the
signed partition formula. -/
theorem grandCanonicalExternalSubsetMomentSeries_mul_normalizedPartition_eq_vertexDysonSeries
    (ε : Mode → ℝ) (β μ : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (times : Fin (2 * E) → ℝ)
    (S : Finset (Fin (2 * E))) (hS : S ≠ ∅) (heven : Even S.card) :
    grandCanonicalExternalSubsetMomentSeries ε β μ g labels times S *
        PowerSeries.normalizeByConstantCoeff
          (Common.dysonTraceSeries (fermionEnergy (fun k => ε k - μ)) β
            (quarticInteraction g)) =
      externalInsertionVertexDysonSeries ε β μ g
        (evenExternalSubsetLabels labels S heven)
        (evenExternalSubsetTimes times S heven) := by
  unfold grandCanonicalExternalSubsetMomentSeries
  rw [externalSubsetChemicalPotentialFactor_eq_family μ labels times S heven]
  simp only [externalSubsetMomentSeries, hS, heven, dite_eq_left]
  exact (externalInsertionVertexDysonSeries_eq_shiftedVacuumFree_mul_normalizedDysonPartitionSeries
    ε β μ hβ g (evenExternalSubsetLabels labels S heven)
      (evenExternalSubsetTimes times S heven)).symm

/-- Transport the physical signed moment theorem by the product of the
external field factors. This preserves the fermionic partition signs exactly. -/
private theorem grandCanonicalExternalSubsetMomentSeries_eq_signedConnected_of_shifted
    (ε : Mode → ℝ) (β μ : ℝ)
    (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (times : Fin (2 * E) → ℝ)
    (hshift : ∀ S : Finset (Fin (2 * E)),
      externalSubsetMomentSeries (fun k => ε k - μ) β g labels times S =
        externalSubsetSignedConnectedMomentSeries (fun k => ε k - μ) β g labels times S)
    (S : Finset (Fin (2 * E))) :
    grandCanonicalExternalSubsetMomentSeries ε β μ g labels times S =
      Finpartition.weightedMomentFromCumulant
        (fun _ π => PowerSeries.C (externalPartitionSourceSign π))
        (grandCanonicalExternalSubsetConnectedDiagramSeries ε β μ g labels times) S := by
  unfold grandCanonicalExternalSubsetMomentSeries grandCanonicalExternalSubsetConnectedDiagramSeries
  rw [Finpartition.weightedMomentFromCumulant_mul_elementWeights, hshift S]
  rfl

/-- The signed physical moment identity at arbitrary real chemical potential.
Only the pre-existing nonnegative inverse-temperature hypothesis is needed. -/
theorem grandCanonicalExternalSubsetMomentSeries_eq_signedConnected
    (ε : Mode → ℝ) (β μ : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (times : Fin (2 * E) → ℝ)
    (S : Finset (Fin (2 * E))) :
    grandCanonicalExternalSubsetMomentSeries ε β μ g labels times S =
      Finpartition.weightedMomentFromCumulant
        (fun _ π => PowerSeries.C (externalPartitionSourceSign π))
        (grandCanonicalExternalSubsetConnectedDiagramSeries ε β μ g labels times) S :=
  grandCanonicalExternalSubsetMomentSeries_eq_signedConnected_of_shifted
    ε β μ g labels times
    (externalSubsetMomentSeries_eq_signedConnected (fun k => ε k - μ) β hβ g labels times) S

/-- The arbitrary-μ connected source cumulant follows from the transported
physical signed moment identity by the existing weighted inversion. -/
private theorem grandCanonicalExternalSubsetSourceCumulantSeries_eq_connected_of_shifted
    (ε : Mode → ℝ) (β μ : ℝ)
    (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (times : Fin (2 * E) → ℝ)
    (hshift : ∀ S : Finset (Fin (2 * E)),
      externalSubsetMomentSeries (fun k => ε k - μ) β g labels times S =
        externalSubsetSignedConnectedMomentSeries (fun k => ε k - μ) β g labels times S) :
    externalSubsetSourceCumulantSeries
        (grandCanonicalExternalSubsetMomentSeries ε β μ g labels times) =
      grandCanonicalExternalSubsetConnectedDiagramSeries ε β μ g labels times := by
  apply externalPartitionWeightedMoment_injective
  · simp [grandCanonicalExternalSubsetConnectedDiagramSeries]
  · intro S
    exact (externalSubsetSourceCumulantSeries_reconstruct
      (grandCanonicalExternalSubsetMomentSeries ε β μ g labels times)
      (by simp [grandCanonicalExternalSubsetMomentSeries]) S).trans
      (grandCanonicalExternalSubsetMomentSeries_eq_signedConnected_of_shifted
        ε β μ g labels times hshift S)

/-- Finite-mode fermionic arbitrary-external linked-cluster theorem at explicit μ:
the physical-H vacuum-normalized source cumulant equals the fully connected
grand-canonical diagram series. -/
theorem grandCanonicalExternalSubsetSourceCumulantSeries_eq_connectedDiagramSeries
    (ε : Mode → ℝ) (β μ : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (times : Fin (2 * E) → ℝ) :
    externalSubsetSourceCumulantSeries
        (grandCanonicalExternalSubsetMomentSeries ε β μ g labels times) =
      grandCanonicalExternalSubsetConnectedDiagramSeries ε β μ g labels times :=
  grandCanonicalExternalSubsetSourceCumulantSeries_eq_connected_of_shifted
    ε β μ g labels times
    (externalSubsetMomentSeries_eq_signedConnected (fun k => ε k - μ) β hβ g labels times)

/-- The direct two-external-insertion source-cumulant theorem retains its
stronger absence of a sign restriction on β at arbitrary chemical potential. -/
theorem grandCanonicalExternalSubsetSourceCumulantSeries_eq_connectedDiagramSeries_two
    (ε : Mode → ℝ) (β μ : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (labels : Fin 2 → ExternalFieldLabel Mode)
    (times : Fin 2 → ℝ) :
    externalSubsetSourceCumulantSeries (E := 1)
        (grandCanonicalExternalSubsetMomentSeries (E := 1) ε β μ g labels times) =
      grandCanonicalExternalSubsetConnectedDiagramSeries (E := 1) ε β μ g labels times :=
  grandCanonicalExternalSubsetSourceCumulantSeries_eq_connected_of_shifted
    (E := 1) ε β μ g labels times
    (externalSubsetMomentSeries_eq_signedConnected_two (fun k => ε k - μ) β g labels times)

end Fermionic
end SecondQuantization
