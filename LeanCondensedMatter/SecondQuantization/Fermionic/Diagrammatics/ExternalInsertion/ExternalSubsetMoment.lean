import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ComponentSign
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.InteractionPictureVertexDyson
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.MixedOrderData
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.ExternalPartition
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

/-- A fixed convention for a partition's fermionic source sign. For partitions
with even blocks the choice of block order does not affect the result. Odd
blocks produce zero terms in the physical connected-diagram product. -/
noncomputable def externalPartitionSourceSign
    {S : Finset (Fin (2 * E))} (π : Finpartition S) : ℂ :=
  externalPartitionOrderSign π (Fintype.equivFin π.parts)

/-- Grouping an external set into a single source block has trivial
fermionic shuffle sign. This is the diagonal normalization needed for the
triangular source moment-to-cumulant transform. -/
theorem externalPartitionSourceSign_top
    (S : Finset (Fin (2 * E))) :
    externalPartitionSourceSign (⊤ : Finpartition S) = 1 := by
  classical
  haveI : Subsingleton (↥(⊤ : Finpartition S).parts) := by
    constructor
    intro B C
    apply Subtype.ext
    have hB : (B : Finset (Fin (2 * E))) = S :=
      Finset.mem_singleton.mp (Finpartition.parts_top_subset S B.2)
    have hC : (C : Finset (Fin (2 * E))) = S :=
      Finset.mem_singleton.mp (Finpartition.parts_top_subset S C.2)
    exact hB.trans hC.symm
  have hzero :
      (externalPartitionShuffle (⊤ : Finpartition S)).orderedBlockInversionCount
          (Fintype.equivFin (⊤ : Finpartition S).parts) = 0 := by
    unfold Combinatorics.FamilySlotShuffleTo.orderedBlockInversionCount
    apply Finset.sum_eq_zero
    intro BC hBC
    have hne := (Finset.mem_offDiag.mp hBC).2.2
    exact (hne (Subsingleton.elim BC.1 BC.2)).elim
  unfold externalPartitionSourceSign externalPartitionOrderSign
  rw [hzero]
  simp

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

/-- A non-top external partition cannot contain the entire ambient source
set as one of its blocks. This strict decrease underpins the recursive
fermionic cumulant inversion, without postulating an unsigned Möbius formula. -/
private theorem externalPartition_part_ssubset_of_ne_top
    {S : Finset (Fin (2 * E))} (π : Finpartition S)
    (hne : π ≠ ⊤) {B : Finset (Fin (2 * E))}
    (hB : B ∈ π.parts) : B ⊂ S := by
  have hsubset : B ⊆ S := π.le hB
  have hproper : B ≠ S := by
    intro hEq
    have htopLe : (⊤ : Finpartition S) ≤ π := by
      intro T hT
      have hT' : T = S :=
        Finset.mem_singleton.mp (Finpartition.parts_top_subset S hT)
      subst T
      exact ⟨B, hB, by simp [hEq]⟩
    exact hne (le_antisymm le_top htopLe)
  exact Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, hproper⟩

/-- The signed external-source moment transform is injective on normalized
connected-block functions (whose empty-set values agree). In particular,
there is no ambiguity in defining connected source cumulants from physical
moments, provided the signed Dyson partition identity is established.

The proof is triangular on proper external subsets: the one-block term has
sign one, and every other partition uses strictly smaller blocks. It does
not apply ordinary unsigned Möbius inversion to signed partition weights. -/
theorem externalPartitionWeightedMoment_injective
    (κ κ' : Finset (Fin (2 * E)) → PowerSeries ℂ)
    (hEmpty : κ ∅ = κ' ∅)
    (hMoments : ∀ S : Finset (Fin (2 * E)),
      Finpartition.weightedMomentFromCumulant
        (fun _ π => PowerSeries.C (externalPartitionSourceSign π)) κ S =
      Finpartition.weightedMomentFromCumulant
        (fun _ π => PowerSeries.C (externalPartitionSourceSign π)) κ' S) :
    κ = κ' := by
  classical
  funext S
  refine Finset.strongInductionOn S ?_
  intro S ih
  by_cases hS : S = ∅
  · simpa only [hS] using hEmpty
  · have hprod (π : Finpartition S) (hne : π ≠ ⊤) :
        Finpartition.partitionProduct κ π =
          Finpartition.partitionProduct κ' π := by
      unfold Finpartition.partitionProduct
      apply Finset.prod_congr rfl
      intro B hB
      exact ih B (externalPartition_part_ssubset_of_ne_top π hne hB)
    have hrest :
        (∑ π ∈ (Finset.univ : Finset (Finpartition S)).erase ⊤,
          PowerSeries.C (externalPartitionSourceSign π) *
            Finpartition.partitionProduct κ π) =
        (∑ π ∈ (Finset.univ : Finset (Finpartition S)).erase ⊤,
          PowerSeries.C (externalPartitionSourceSign π) *
            Finpartition.partitionProduct κ' π) := by
      apply Finset.sum_congr rfl
      intro π hπ
      rw [hprod π (Finset.mem_erase.mp hπ).1]
    have hsource := hMoments S
    unfold Finpartition.weightedMomentFromCumulant at hsource
    rw [← Finset.sum_erase_add Finset.univ
      (fun π : Finpartition S =>
        PowerSeries.C (externalPartitionSourceSign π) *
          Finpartition.partitionProduct κ π) (Finset.mem_univ ⊤),
      ← Finset.sum_erase_add Finset.univ
      (fun π : Finpartition S =>
        PowerSeries.C (externalPartitionSourceSign π) *
          Finpartition.partitionProduct κ' π) (Finset.mem_univ ⊤)] at hsource
    rw [hrest] at hsource
    have htop (k : Finset (Fin (2 * E)) → PowerSeries ℂ) :
        PowerSeries.C (externalPartitionSourceSign (⊤ : Finpartition S)) *
          Finpartition.partitionProduct k (⊤ : Finpartition S) = k S := by
      rw [externalPartitionSourceSign_top, Finpartition.partitionProduct_top hS]
      simp
    rw [htop κ, htop κ'] at hsource
    exact add_left_cancel hsource

/-- Finite fermionic source cumulants, defined recursively from the complete
subset moment function. The recursion is along *strict* subset, since only
non-top partitions require values at proper blocks. No Grassmann algebra and
no unjustified ordinary unsigned partition inversion are introduced. -/
noncomputable def externalSubsetSourceCumulantSeries
    (M : Finset (Fin (2 * E)) → PowerSeries ℂ) :
    Finset (Fin (2 * E)) → PowerSeries ℂ := by
  classical
  let wf : WellFounded
      (fun T S : Finset (Fin (2 * E)) => T ⊂ S) := inferInstance
  exact wf.fix (fun S ih =>
    if S = ∅ then 0
    else M S -
      ∑ π : {π : Finpartition S // π ≠ ⊤},
        PowerSeries.C (externalPartitionSourceSign π.1) *
          ∏ B : π.1.parts,
            ih (B : Finset (Fin (2 * E)))
              (externalPartition_part_ssubset_of_ne_top π.1 π.2 B.2))

/-- The recursive source cumulant is normalized to zero on empty insertion
sets. The normalized empty source moment, in contrast, is one. -/
@[simp]
theorem externalSubsetSourceCumulantSeries_empty
    (M : Finset (Fin (2 * E)) → PowerSeries ℂ) :
    externalSubsetSourceCumulantSeries M ∅ = 0 := by
  classical
  unfold externalSubsetSourceCumulantSeries
  rw [WellFounded.fix_eq]
  simp

/-- The defining triangular equation for fermionic source cumulants. -/
theorem externalSubsetSourceCumulantSeries_eq_sub_properPartitions
    (M : Finset (Fin (2 * E)) → PowerSeries ℂ)
    (S : Finset (Fin (2 * E))) (hS : S ≠ ∅) :
    externalSubsetSourceCumulantSeries M S =
      M S -
        ∑ π : {π : Finpartition S // π ≠ ⊤},
          PowerSeries.C (externalPartitionSourceSign π.1) *
            Finpartition.partitionProduct (externalSubsetSourceCumulantSeries M) π.1 := by
  classical
  unfold externalSubsetSourceCumulantSeries
  rw [WellFounded.fix_eq]
  simp only [hS, ite_false]
  congr 1
  apply Finset.sum_congr rfl
  intro π _
  apply congrArg (fun z : PowerSeries ℂ =>
    PowerSeries.C (externalPartitionSourceSign π.1) * z)
  change (∏ B : π.1.parts,
      externalSubsetSourceCumulantSeries M (B : Finset (Fin (2 * E)))) =
    Finpartition.partitionProduct (externalSubsetSourceCumulantSeries M) π.1
  exact Finset.prod_coe_sort π.1.parts
    (externalSubsetSourceCumulantSeries M)

/-- The signed source moment transform is inverted by finite subset
recursion, provided the empty moment is one. This supplies an explicit
fermionic cumulant/source convention before any physical n-point theorem.
No assumption about diagram factorization is needed for this algebraic step. -/
theorem externalSubsetSourceCumulantSeries_reconstruct
    (M : Finset (Fin (2 * E)) → PowerSeries ℂ)
    (hEmpty : M ∅ = 1)
    (S : Finset (Fin (2 * E))) :
    Finpartition.weightedMomentFromCumulant
      (fun _ π => PowerSeries.C (externalPartitionSourceSign π))
      (externalSubsetSourceCumulantSeries M) S = M S := by
  classical
  let κ := externalSubsetSourceCumulantSeries M
  by_cases hS : S = ∅
  · subst S
    letI : Unique (Finpartition (∅ : Finset (Fin (2 * E)))) :=
      inferInstanceAs (Unique (Finpartition (⊥ : Finset (Fin (2 * E)))))
    unfold Finpartition.weightedMomentFromCumulant
    rw [Fintype.sum_unique]
    have htop : (default : Finpartition (∅ : Finset (Fin (2 * E)))) = ⊤ :=
      Subsingleton.elim _ _
    rw [htop]
    change PowerSeries.C (externalPartitionSourceSign (⊤ : Finpartition (∅ : Finset (Fin (2 * E))))) *
      Finpartition.partitionProduct (externalSubsetSourceCumulantSeries M) ⊤ = M ∅
    rw [externalPartitionSourceSign_top]
    have hparts : (⊤ : Finpartition (∅ : Finset (Fin (2 * E)))).parts = ∅ := by
      simp [Finpartition.parts_eq_empty_iff]
    simp [Finpartition.partitionProduct, hparts, hEmpty]
  · let f : Finpartition S → PowerSeries ℂ := fun π =>
      PowerSeries.C (externalPartitionSourceSign π) *
        Finpartition.partitionProduct κ π
    have hrest :
        (∑ π ∈ (Finset.univ : Finset (Finpartition S)).erase ⊤, f π) =
          ∑ π : {π : Finpartition S // π ≠ ⊤}, f π.1 := by
      rw [Finset.sum_subtype
        (p := fun π : Finpartition S => π ≠ ⊤)
        ((Finset.univ : Finset (Finpartition S)).erase ⊤)
        (fun π => by simp) f]
    have htop : f (⊤ : Finpartition S) = κ S := by
      change PowerSeries.C (externalPartitionSourceSign (⊤ : Finpartition S)) *
        Finpartition.partitionProduct κ (⊤ : Finpartition S) = κ S
      rw [externalPartitionSourceSign_top, Finpartition.partitionProduct_top hS]
      simp
    have hsum :
        Finpartition.weightedMomentFromCumulant
          (fun _ π => PowerSeries.C (externalPartitionSourceSign π)) κ S =
        (∑ π ∈ (Finset.univ : Finset (Finpartition S)).erase ⊤, f π) + κ S := by
      change (∑ π : Finpartition S, f π) = _
      rw [← Finset.sum_erase_add Finset.univ f (Finset.mem_univ (⊤ : Finpartition S))]
      rw [htop]
    have hrec := externalSubsetSourceCumulantSeries_eq_sub_properPartitions M S hS
    change κ S = M S -
      ∑ π : {π : Finpartition S // π ≠ ⊤}, f π.1 at hrec
    calc
      Finpartition.weightedMomentFromCumulant
          (fun _ π => PowerSeries.C (externalPartitionSourceSign π)) κ S =
          (∑ π ∈ (Finset.univ : Finset (Finpartition S)).erase ⊤, f π) + κ S := hsum
      _ = (∑ π : {π : Finpartition S // π ≠ ⊤}, f π.1) + κ S := by rw [hrest]
      _ = (∑ π : {π : Finpartition S // π ≠ ⊤}, f π.1) +
            (M S - ∑ π : {π : Finpartition S // π ≠ ⊤}, f π.1) := by rw [hrec]
      _ = M S := by abel

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
