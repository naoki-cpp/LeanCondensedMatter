import LeanCondensedMatter.Analysis.OrderedSimplex.StrictAntiCongr
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Ordered
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.SlotSplit.SupportStandardization
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.OwnerSlotCongr
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.Amplitude

set_option linter.style.header false

/-!
# Ordered-simplex amplitudes of external-insertion diagrams

Integrate one diagram's fixed-time amplitude, with or without the Dyson sign, using either its
consecutive interaction slots or an explicit interaction order. Component factorization and
shuffle sums are separate consumers of these amplitudes.
-/

namespace SecondQuantization
namespace Fermionic

open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Ordered-simplex contribution of one arbitrary external-insertion diagram, before the Dyson
sign. -/
noncomputable def ExternalInsertionWickDiagram.orderedSimplexContribution
    {E n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) : ℂ :=
  intervalIntegral.orderedSimplexIntegral n β
    (fun σ => d.fixedTimeAmplitude ε β g externalTime σ)

/-- Integrated arbitrary-external-insertion amplitude including the order-`n` Dyson sign. -/
noncomputable def ExternalInsertionWickDiagram.dysonAmplitude
    {E n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) : ℂ :=
  (-1 : ℂ) ^ n * d.orderedSimplexContribution ε β g externalTime


/-- Dyson amplitude with the interaction vertices assigned to the ordered-simplex slots by an
explicit global interaction order. -/
noncomputable def ExternalInsertionWickDiagram.orderedDysonAmplitude
    {E n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ)
    (order : QuarticVertexOrder (Finset.univ : Finset (Fin n))) : ℂ :=
  intervalIntegral.orderedSimplexIntegral
    (Finset.univ : Finset (Fin n)).card β
    (fun τ =>
      d.dysonFixedTimeAmplitude ε β g externalTime
        (fun v => τ (order.symm ⟨v, Finset.mem_univ v⟩)))

/-- Integrating the Dyson-signed fixed-time amplitude is the integrated Dyson amplitude. -/
theorem ExternalInsertionWickDiagram.orderedSimplexIntegral_dysonFixedTimeAmplitude
    {E n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) :
    intervalIntegral.orderedSimplexIntegral n β
        (fun σ => d.dysonFixedTimeAmplitude ε β g externalTime σ) =
      d.dysonAmplitude ε β g externalTime := by
  unfold ExternalInsertionWickDiagram.dysonFixedTimeAmplitude
    ExternalInsertionWickDiagram.dysonAmplitude
    ExternalInsertionWickDiagram.orderedSimplexContribution
  exact intervalIntegral.orderedSimplexIntegral_smul n β
    ((-1 : ℂ) ^ n) (fun σ => d.fixedTimeAmplitude ε β g externalTime σ)

/-- The physical Dyson amplitude is the ordered-simplex amplitude for
the increasing ambient interaction order. No factorial is introduced. -/
theorem ExternalInsertionWickDiagram.orderedDysonAmplitude_canonicalOrder
    {E n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) :
    d.orderedDysonAmplitude ε β g externalTime
      ((Finset.univ : Finset (Fin n)).orderIsoOfFin rfl).toEquiv =
      d.dysonAmplitude ε β g externalTime := by
  classical
  unfold ExternalInsertionWickDiagram.orderedDysonAmplitude
  rw [← d.orderedSimplexIntegral_dysonFixedTimeAmplitude ε β g externalTime]
  have hcard : (Finset.univ : Finset (Fin n)).card = n := by simp
  calc
    intervalIntegral.orderedSimplexIntegral
        (Finset.univ : Finset (Fin n)).card β
        (fun τ => d.dysonFixedTimeAmplitude ε β g externalTime
          (fun v => τ
            (((Finset.univ : Finset (Fin n)).orderIsoOfFin rfl).toEquiv.symm
              ⟨v, Finset.mem_univ v⟩))) =
      intervalIntegral.orderedSimplexIntegral n β
        (fun τ => d.dysonFixedTimeAmplitude ε β g externalTime
          (fun v => τ
            (Fin.cast hcard
              (((Finset.univ : Finset (Fin n)).orderIsoOfFin rfl).toEquiv.symm
                ⟨v, Finset.mem_univ v⟩)))) :=
        intervalIntegral.orderedSimplexIntegral_cast hcard β _
    _ = intervalIntegral.orderedSimplexIntegral n β
          (fun τ => d.dysonFixedTimeAmplitude ε β g externalTime τ) := by
      apply intervalIntegral.orderedSimplexIntegral_congr
      intro τ
      apply congrArg (d.dysonFixedTimeAmplitude ε β g externalTime)
      funext v
      apply congrArg τ
      apply Fin.ext
      simp only [Fin.val_cast]
      change (((Finset.univ : Finset (Fin n)).orderIsoOfFin rfl).symm
        ⟨v, Finset.mem_univ v⟩).val = v.val
      rw [Finset.orderIsoOfFin_symm_apply]
      simp only [Fin.sort_univ, List.idxOf_finRange]


/-- Every strictly decreasing ordered-simplex time assignment remains
injective after pulling it back along an arbitrary global interaction
vertex order. Thus interaction-vertex time collisions can be discarded
when checking an ordered Dyson amplitude identity. -/
theorem quarticVertexOrderedTime_injective_of_strictAnti
    {n : ℕ}
    (order : QuarticVertexOrder (Finset.univ : Finset (Fin n)))
    (τ : Fin (Finset.univ : Finset (Fin n)).card → ℝ)
    (hτ : StrictAnti τ) :
    Function.Injective
      (fun v : Fin n => τ (order.symm ⟨v, Finset.mem_univ v⟩)) := by
  intro a b hab
  have h := order.symm.injective (hτ.injective hab)
  exact congrArg Subtype.val h

/-- A Dyson-amplitude covariance identity needs to be checked only on
strictly decreasing ambient time slots, assuming the physical inverse
temperature interval satisfies `0 ≤ β`.

The pointwise hypothesis is deliberately about the **full Dyson-signed
Wick amplitude**, not just the individual pair contraction. Relabeling
four-leg vertices changes the mixed-time pairing normalization and its
fermionic sign; those must cancel before this integral theorem applies.
Equal-time tie breakers do not enter the integral equality. -/
theorem ExternalInsertionWickDiagram.orderedDysonAmplitude_congr_of_strictAnti
    {E n : ℕ}
    (d d' : ExternalInsertionWickDiagram Mode E n)
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ)
    (order order' : QuarticVertexOrder (Finset.univ : Finset (Fin n)))
    (hpoint : ∀ τ : Fin (Finset.univ : Finset (Fin n)).card → ℝ,
      StrictAnti τ → (∀ i, τ i < β) →
        d.dysonFixedTimeAmplitude ε β g externalTime
          (fun v => τ (order.symm ⟨v, Finset.mem_univ v⟩)) =
        d'.dysonFixedTimeAmplitude ε β g externalTime
          (fun v => τ (order'.symm ⟨v, Finset.mem_univ v⟩))) :
    d.orderedDysonAmplitude ε β g externalTime order =
      d'.orderedDysonAmplitude ε β g externalTime order' := by
  unfold ExternalInsertionWickDiagram.orderedDysonAmplitude
  exact intervalIntegral.orderedSimplexIntegral_congr_of_strictAnti
    _ β hβ _ _ hpoint



/-- The *integrated* physical Dyson contribution is invariant when
interaction-vertex slots are relabeled together with the global
interaction order.

The key input is exact equality of the **full** Dyson-signed Wick
amplitudes on injective-time assignments. On the ordered simplex,
injectivity follows from strict antitonicity almost everywhere; the
strict-chamber congruence already accounts for the lower-dimensional
time-collision set. Importantly, the order must be transported along
`e`: the canonical-order integral need not be invariant under an
arbitrary permutation when the order is held fixed. -/
theorem ExternalInsertionWickDiagram.orderedDysonAmplitude_slotCongr
    {E n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (e : ↥(Finset.univ : Finset (Fin n)) ≃
      ↥(Finset.univ : Finset (Fin n)))
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ)
    (order : QuarticVertexOrder (Finset.univ : Finset (Fin n))) :
    d.orderedDysonAmplitude ε β g externalTime order =
      ExternalInsertionWickDiagram.orderedDysonAmplitude (d.slotCongr e) ε β g externalTime
        (order.trans e) := by
  apply d.orderedDysonAmplitude_congr_of_strictAnti
    (d.slotCongr e) ε β hβ g externalTime order (order.trans e)
  intro τ hτ _
  let σ : Fin n → ℝ :=
    fun v => τ (order.symm ⟨v, Finset.mem_univ v⟩)
  have hσ : Function.Injective σ :=
    quarticVertexOrderedTime_injective_of_strictAnti order τ hτ
  have htime :
      (fun v : Fin n => τ ((order.trans e).symm ⟨v, Finset.mem_univ v⟩)) =
        σ ∘ fun v => (e.symm ⟨v, Finset.mem_univ v⟩).1 := by
    funext v
    rfl
  change d.dysonFixedTimeAmplitude ε β g externalTime σ =
    ExternalInsertionWickDiagram.dysonFixedTimeAmplitude (d.slotCongr e) ε β g externalTime
      (fun v => τ ((order.trans e).symm ⟨v, Finset.mem_univ v⟩))
  rw [htime]
  exact (d.slotCongr_dysonFixedTimeAmplitude_eq_of_injective
    e ε β g externalTime σ hσ).symm



/-- A canonical Dyson integral of one **physical** diagram is the
ordered-simplex amplitude of its relabeled diagram with the global
interaction order transported accordingly. This is the exact termwise
bridge needed before reindexing the physical fixed-partition fiber:
it does **not** assert invariance of individual canonical Dyson
integrals under arbitrary interaction-slot permutations. -/
theorem ExternalInsertionWickDiagram.dysonAmplitude_eq_slotCongr_orderedDysonAmplitude
    {E n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (e : ↥(Finset.univ : Finset (Fin n)) ≃
      ↥(Finset.univ : Finset (Fin n)))
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) :
    d.dysonAmplitude ε β g externalTime =
      ExternalInsertionWickDiagram.orderedDysonAmplitude (d.slotCongr e)
        ε β g externalTime
        (((Finset.univ : Finset (Fin n)).orderIsoOfFin rfl).toEquiv.trans e) := by
  calc
    d.dysonAmplitude ε β g externalTime =
        d.orderedDysonAmplitude ε β g externalTime
          ((Finset.univ : Finset (Fin n)).orderIsoOfFin rfl).toEquiv :=
      (d.orderedDysonAmplitude_canonicalOrder ε β g externalTime).symm
    _ = _ :=
      d.orderedDysonAmplitude_slotCongr e ε β hβ g externalTime
        ((Finset.univ : Finset (Fin n)).orderIsoOfFin rfl).toEquiv

open Classical in
/-- At one fixed *physical external-component partition*, the genuine
vacuum-free fixed-label Dyson diagram sum is unchanged if its canonical
interaction-time order is replaced by any common reindexed order,
**after the actual Wick diagram fiber has been reindexed** by the same
interaction-slot permutation.

This identifies the physical owner-assignment sector across vertex
renumberings, with neither an extra factorial nor a quotient of
fermionic pairing orientations. In contrast to an individual diagram,
this statement holds after summing all diagrams with the prescribed
external labels and graph-induced external partition. -/
theorem sum_fixedPartitionDysonAmplitude_eq_reindexedOrderedDysonAmplitude
    {E n : ℕ}
    (π : Finpartition (Finset.univ : Finset (Fin (2 * E))))
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ)
    (e : ↥(Finset.univ : Finset (Fin n)) ≃
      ↥(Finset.univ : Finset (Fin n))) :
    (∑ d : {d : {d : ExternalInsertionWickDiagram Mode E n //
        HasNoVacuumComponent d.vertexGraph} //
        externalComponentPartition d.1.vertexGraph = π},
      if d.1.1.externalLabel = labels then
        d.1.1.dysonAmplitude ε β g externalTime else 0) =
      ∑ d : {d : {d : ExternalInsertionWickDiagram Mode E n //
          HasNoVacuumComponent d.vertexGraph} //
          externalComponentPartition d.1.vertexGraph = π},
        if d.1.1.externalLabel = labels then
          d.1.1.orderedDysonAmplitude ε β g externalTime
            (((Finset.univ : Finset (Fin n)).orderIsoOfFin rfl).toEquiv.trans e)
        else 0 := by
  let fiber := {d : {d : ExternalInsertionWickDiagram Mode E n //
      HasNoVacuumComponent d.vertexGraph} //
      externalComponentPartition d.1.vertexGraph = π}
  let φ : fiber ≃ fiber :=
    ExternalInsertionDiagram.fixedPartitionVacuumFreeSlotCongrEquiv
      (E := E) (N := n) (M := n) e π
  let weight : fiber → ℂ := fun d =>
    if d.1.1.externalLabel = labels then
      d.1.1.orderedDysonAmplitude ε β g externalTime
        (((Finset.univ : Finset (Fin n)).orderIsoOfFin rfl).toEquiv.trans e)
    else 0
  have hterm (d : fiber) :
      (if d.1.1.externalLabel = labels then
        d.1.1.dysonAmplitude ε β g externalTime else 0) =
        weight (φ d) := by
    change (if d.1.1.externalLabel = labels then
        d.1.1.dysonAmplitude ε β g externalTime else 0) =
      (if (d.1.1.slotCongr e).externalLabel = labels then
        ExternalInsertionWickDiagram.orderedDysonAmplitude (d.1.1.slotCongr e)
          ε β g externalTime
          (((Finset.univ : Finset (Fin n)).orderIsoOfFin rfl).toEquiv.trans e)
      else 0)
    rw [ExternalInsertionDiagram.slotCongr_externalLabel]
    exact if_congr Iff.rfl
      (d.1.1.dysonAmplitude_eq_slotCongr_orderedDysonAmplitude
        e ε β hβ g externalTime) rfl
  calc
    (∑ d : fiber, if d.1.1.externalLabel = labels then
        d.1.1.dysonAmplitude ε β g externalTime else 0) =
      ∑ d : fiber, weight (φ d) := by
        apply Finset.sum_congr rfl
        intro d _
        exact hterm d
    _ = ∑ d : fiber, weight d := Equiv.sum_comp φ weight
    _ = _ := rfl


open Classical in
/-- The actual fixed-label, fixed-external-partition physical Dyson
coefficient is a finite sum over **realized** interaction-size vectors,
owner shuffles and standardized connected local Wick diagrams.

The integrand on the right retains its *transported global Dyson order*.
This composes the exact physical ordered-amplitude covariance with the
combinatorial standardized-size/shuffle equivalence. It introduces no
extra factorial or independence assumption: factorizing the remaining
owner-shuffle sum into local Dyson coefficients is a separate obligation. -/
theorem sum_fixedPartitionDysonAmplitude_eq_standardizedOrderedDysonAmplitude
    {E n : ℕ}
    (anchor : Fin (2 * E))
    (π : Finpartition (Finset.univ : Finset (Fin (2 * E))))
    (heven : ∀ B : π.parts, Even (B : Finset (Fin (2 * E))).card)
    (labels : Fin (2 * E) → ExternalFieldLabel Mode)
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ)
    (e : ↥(Finset.univ : Finset (Fin n)) ≃
      ↥(Finset.univ : Finset (Fin n))) :
    (∑ d : {d : {d : ExternalInsertionWickDiagram Mode E n //
        HasNoVacuumComponent d.vertexGraph} //
        externalComponentPartition d.1.vertexGraph = π},
      if d.1.1.externalLabel = labels then
        d.1.1.dysonAmplitude ε β g externalTime else 0) =
      ∑ p ∈ ExternalInsertionBlockLayout.fixedPartitionPhysicalStandardizedSizeShuffleFiniteDomain
          (E := E) (N := n) (ExternalLabel := ExternalFieldLabel Mode)
          (InternalLabel := QuarticVertexLabel Mode) anchor π heven,
        if ((ExternalInsertionBlockLayout.fixedPartitionPhysicalStandardizedSizeShuffleEquiv
              (E := E) (N := n) (ExternalLabel := ExternalFieldLabel Mode)
              (InternalLabel := QuarticVertexLabel Mode) anchor π heven).symm p).1.1.externalLabel =
            labels then
          ExternalInsertionWickDiagram.orderedDysonAmplitude
            ((ExternalInsertionBlockLayout.fixedPartitionPhysicalStandardizedSizeShuffleEquiv
              (E := E) (N := n) (ExternalLabel := ExternalFieldLabel Mode)
              (InternalLabel := QuarticVertexLabel Mode) anchor π heven).symm p).1.1
            ε β g externalTime
            (((Finset.univ : Finset (Fin n)).orderIsoOfFin rfl).toEquiv.trans e)
        else 0 := by
  rw [sum_fixedPartitionDysonAmplitude_eq_reindexedOrderedDysonAmplitude
    π labels ε β hβ g externalTime e]
  exact ExternalInsertionBlockLayout.sum_fixedPartitionPhysical_eq_standardized_sizes_shuffles
    (E := E) (N := n) (ExternalLabel := ExternalFieldLabel Mode)
    (InternalLabel := QuarticVertexLabel Mode) anchor π heven
    (fun d => if d.1.1.externalLabel = labels then
      ExternalInsertionWickDiagram.orderedDysonAmplitude d.1.1 ε β g externalTime
        (((Finset.univ : Finset (Fin n)).orderIsoOfFin rfl).toEquiv.trans e)
      else 0)


/-- Relabeling the **physical** interaction vertices converts its canonical
Dyson integral into the corresponding transported-order integral of the
original Wick diagram. This is the reverse direction of
`dysonAmplitude_eq_slotCongr_orderedDysonAmplitude`, and notably it does
*not* identify the two canonical-order integrals. -/
theorem ExternalInsertionWickDiagram.slotCongr_dysonAmplitude_eq_orderedDysonAmplitude
    {E n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (e : ↥(Finset.univ : Finset (Fin n)) ≃
      ↥(Finset.univ : Finset (Fin n)))
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) :
    ExternalInsertionWickDiagram.dysonAmplitude (d.slotCongr e)
      ε β g externalTime =
      d.orderedDysonAmplitude ε β g externalTime
        (((Finset.univ : Finset (Fin n)).orderIsoOfFin rfl).toEquiv.trans e.symm) := by
  have hback : (d.slotCongr e).slotCongr e.symm = d :=
    (ExternalInsertionDiagram.slotCongrEquiv
      (E := E) (ExternalLabel := ExternalFieldLabel Mode)
      (InternalLabel := QuarticVertexLabel Mode) e).left_inv d
  calc
    ExternalInsertionWickDiagram.dysonAmplitude (d.slotCongr e)
        ε β g externalTime =
      ExternalInsertionWickDiagram.orderedDysonAmplitude
        ((d.slotCongr e).slotCongr e.symm)
        ε β g externalTime
          (((Finset.univ : Finset (Fin n)).orderIsoOfFin rfl).toEquiv.trans e.symm) :=
      ExternalInsertionWickDiagram.dysonAmplitude_eq_slotCongr_orderedDysonAmplitude
        (d.slotCongr e) e.symm ε β hβ g externalTime
    _ = _ := by rw [hback]

open Classical in
/-- For a finite family of physical Wick diagrams obtained by *actual
interaction-slot relabelings of one fixed diagram*, the full canonical
Dyson sum is exactly its transported global-order orbit sum. The orbit
is counted by the supplied finite index type, with no extra factorial.
To apply this to physical owner assignments one must prove the assembly
transport identity for the standardized connected-block family. -/
theorem ExternalInsertionWickDiagram.sum_slotCongr_dysonAmplitude_eq_orderedDysonOrbit
    {E n : ℕ} {I : Type*} [Fintype I]
    (d : ExternalInsertionWickDiagram Mode E n)
    (relabel : I → (↥(Finset.univ : Finset (Fin n)) ≃
      ↥(Finset.univ : Finset (Fin n))))
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) :
    (∑ i : I, ExternalInsertionWickDiagram.dysonAmplitude
      (d.slotCongr (relabel i)) ε β g externalTime) =
      ∑ i : I, d.orderedDysonAmplitude ε β g externalTime
        (((Finset.univ : Finset (Fin n)).orderIsoOfFin rfl).toEquiv.trans
          (relabel i).symm) := by
  apply Finset.sum_congr rfl
  intro i _
  exact d.slotCongr_dysonAmplitude_eq_orderedDysonAmplitude
    (relabel i) ε β hβ g externalTime


open Classical in
/-- Physical interaction-owner shuffle orbit of an actually assembled
family of labelled Wick diagrams equals the ordered Dyson integral
orbit of one fixed assembled reference diagram. The local data are
transported with their actual vertex owners, preserving pairing data;
the result does not assume diagramwise canonical integral invariance. -/
theorem ExternalInsertionBlockLayout.sum_assembledOwnerShuffle_dysonAmplitude_eq_orderedDysonOrbit
    {E n : ℕ}
    (layout : ExternalInsertionBlockLayout E n)
    {size : layout.partition.parts → ℕ}
    (reference : Combinatorics.FamilySlotShuffleTo size n)
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram (ExternalFieldLabel Mode) (QuarticVertexLabel Mode)
        ((B : Finset (Fin (2 * E))).card / 2) n
        (layout.interactionBlock (Finset.univ : Finset (Fin n)) B))
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) :
    (∑ shuffle : Combinatorics.FamilySlotShuffleTo size n,
      ExternalInsertionWickDiagram.dysonAmplitude
        ((layout.ownerSlotCongr (reference.ambientRelabel shuffle)).assembleDiagram
          (Finset.univ : Finset (Fin n))
          (layout.ownerSlotCongrBlockFamily
            (reference.ambientRelabel shuffle) F))
        ε β g externalTime) =
      ∑ shuffle : Combinatorics.FamilySlotShuffleTo size n,
        ExternalInsertionWickDiagram.orderedDysonAmplitude
          (layout.assembleDiagram (Finset.univ : Finset (Fin n)) F)
          ε β g externalTime
          (((Finset.univ : Finset (Fin n)).orderIsoOfFin rfl).toEquiv.trans
            (fullInteractionSlotEquiv (reference.ambientRelabel shuffle)).symm) := by
  apply Finset.sum_congr rfl
  intro shuffle _
  rw [layout.assembleDiagram_ownerSlotCongr
    (reference.ambientRelabel shuffle) F]
  exact ExternalInsertionWickDiagram.slotCongr_dysonAmplitude_eq_orderedDysonAmplitude
    (layout.assembleDiagram (Finset.univ : Finset (Fin n)) F)
    (fullInteractionSlotEquiv (reference.ambientRelabel shuffle))
    ε β hβ g externalTime


open Classical in
/-- The **entire finite sum over independently preconnected Wick-block
families** at a physically relabeled owner assignment equals the sum of
transported-order Dyson amplitudes over the original connected families.

The summed diagrams retain every labelled pairing; unlike a
diagram-by-diagram canonical-amplitude assertion, each relabeled
canonical integral is evaluated with its corresponding global Dyson
order. This bridges physical owner-family reindexing to integration. -/
theorem ExternalInsertionBlockLayout.sum_ownerSlotCongr_connectedDyson_eq_ordered
    {E n : ℕ}
    (layout : ExternalInsertionBlockLayout E n) (e : Fin n ≃ Fin n)
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) :
    (∑ G : (layout.ownerSlotCongr e).ConnectedBlockFamily
        (ExternalLabel := ExternalFieldLabel Mode)
        (InternalLabel := QuarticVertexLabel Mode),
      ExternalInsertionWickDiagram.dysonAmplitude
        ((layout.ownerSlotCongr e).assembleDiagram
          (Finset.univ : Finset (Fin n)) G.1)
        ε β g externalTime) =
      ∑ F : layout.ConnectedBlockFamily
          (ExternalLabel := ExternalFieldLabel Mode)
          (InternalLabel := QuarticVertexLabel Mode),
        ExternalInsertionWickDiagram.orderedDysonAmplitude
          (layout.assembleDiagram (Finset.univ : Finset (Fin n)) F.1)
          ε β g externalTime
          (((Finset.univ : Finset (Fin n)).orderIsoOfFin rfl).toEquiv.trans
            (fullInteractionSlotEquiv e).symm) := by
  let weight : (layout.ownerSlotCongr e).ConnectedBlockFamily
      (ExternalLabel := ExternalFieldLabel Mode)
      (InternalLabel := QuarticVertexLabel Mode) → ℂ :=
    fun G => ExternalInsertionWickDiagram.dysonAmplitude
      ((layout.ownerSlotCongr e).assembleDiagram
        (Finset.univ : Finset (Fin n)) G.1) ε β g externalTime
  change (∑ G, weight G) = _
  rw [← layout.sum_ownerSlotCongrConnectedBlockFamilies e weight]
  apply Finset.sum_congr rfl
  intro F _
  dsimp [weight]
  have hfamily :
      (layout.ownerSlotCongrConnectedBlockFamilyEquiv e F).1 =
        layout.ownerSlotCongrBlockFamily e F.1 := by
    funext B
    exact layout.ownerSlotCongrConnectedBlockFamilyEquiv_apply e F B
  rw [hfamily, layout.assembleDiagram_ownerSlotCongr e F.1]
  exact ExternalInsertionWickDiagram.slotCongr_dysonAmplitude_eq_orderedDysonAmplitude
    (layout.assembleDiagram (Finset.univ : Finset (Fin n)) F.1)
    (fullInteractionSlotEquiv e) ε β hβ g externalTime



open Classical in
/-- The physical connected-block Dyson sum with a prescribed **independent
external source label on every block** is reindexed across any
interaction-owner relabeling. Exact block source labels are unchanged;
the global Dyson order is transported, not replaced by the canonical
order of a different physical diagram.

This label-aware version is the form needed for the fixed-external-
partition coefficientwise signed moment identity. -/
theorem ExternalInsertionBlockLayout.sum_ownerSlotCongr_connectedDyson_eq_ordered_localLabels
    {E n : ℕ}
    (layout : ExternalInsertionBlockLayout E n) (e : Fin n ≃ Fin n)
    (localLabels : ∀ B : layout.partition.parts,
      Fin (2 * ((B : Finset (Fin (2 * E))).card / 2)) →
        ExternalFieldLabel Mode)
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) :
    (∑ G : (layout.ownerSlotCongr e).ConnectedBlockFamily
        (ExternalLabel := ExternalFieldLabel Mode)
        (InternalLabel := QuarticVertexLabel Mode),
      if ∀ B : (layout.ownerSlotCongr e).partition.parts,
          (G.1 B).externalLabel = localLabels B then
        ExternalInsertionWickDiagram.dysonAmplitude
          ((layout.ownerSlotCongr e).assembleDiagram
            (Finset.univ : Finset (Fin n)) G.1)
          ε β g externalTime
      else 0) =
      ∑ F : layout.ConnectedBlockFamily
          (ExternalLabel := ExternalFieldLabel Mode)
          (InternalLabel := QuarticVertexLabel Mode),
        if ∀ B : layout.partition.parts,
            (F.1 B).externalLabel = localLabels B then
          ExternalInsertionWickDiagram.orderedDysonAmplitude
            (layout.assembleDiagram (Finset.univ : Finset (Fin n)) F.1)
            ε β g externalTime
            (((Finset.univ : Finset (Fin n)).orderIsoOfFin rfl).toEquiv.trans
              (fullInteractionSlotEquiv e).symm)
        else 0 := by
  let weight : (layout.ownerSlotCongr e).ConnectedBlockFamily
      (ExternalLabel := ExternalFieldLabel Mode)
      (InternalLabel := QuarticVertexLabel Mode) → ℂ :=
    fun G =>
      if ∀ B : (layout.ownerSlotCongr e).partition.parts,
          (G.1 B).externalLabel = localLabels B then
        ExternalInsertionWickDiagram.dysonAmplitude
          ((layout.ownerSlotCongr e).assembleDiagram
            (Finset.univ : Finset (Fin n)) G.1)
          ε β g externalTime
      else 0
  change (∑ G, weight G) = _
  rw [← layout.sum_ownerSlotCongrConnectedBlockFamilies e weight]
  apply Finset.sum_congr rfl
  intro F _
  dsimp [weight]
  have hlabel (B : layout.partition.parts) :
      ((layout.ownerSlotCongrConnectedBlockFamilyEquiv e F).1 B).externalLabel =
        (F.1 B).externalLabel := by
    rw [layout.ownerSlotCongrConnectedBlockFamilyEquiv_apply e F B]
    rfl
  have hcondition :
      (∀ B : (layout.ownerSlotCongr e).partition.parts,
        ((layout.ownerSlotCongrConnectedBlockFamilyEquiv e F).1 B).externalLabel =
          localLabels B) ↔
        (∀ B : layout.partition.parts, (F.1 B).externalLabel = localLabels B) := by
    constructor
    · intro h B
      exact (hlabel B).symm.trans (h B)
    · intro h B
      exact (hlabel B).trans (h B)
  have hfamily :
      (layout.ownerSlotCongrConnectedBlockFamilyEquiv e F).1 =
        layout.ownerSlotCongrBlockFamily e F.1 := by
    funext B
    exact layout.ownerSlotCongrConnectedBlockFamilyEquiv_apply e F B
  have hamplitude :
      ExternalInsertionWickDiagram.dysonAmplitude
          ((layout.ownerSlotCongr e).assembleDiagram
            (Finset.univ : Finset (Fin n))
            (layout.ownerSlotCongrConnectedBlockFamilyEquiv e F).1)
          ε β g externalTime =
        ExternalInsertionWickDiagram.orderedDysonAmplitude
          (layout.assembleDiagram (Finset.univ : Finset (Fin n)) F.1)
          ε β g externalTime
          (((Finset.univ : Finset (Fin n)).orderIsoOfFin rfl).toEquiv.trans
            (fullInteractionSlotEquiv e).symm) := by
    rw [hfamily, layout.assembleDiagram_ownerSlotCongr e F.1]
    exact ExternalInsertionWickDiagram.slotCongr_dysonAmplitude_eq_orderedDysonAmplitude
      (layout.assembleDiagram (Finset.univ : Finset (Fin n)) F.1)
      (fullInteractionSlotEquiv e) ε β hβ g externalTime
  exact if_congr hcondition hamplitude rfl



open Classical in
/-- At fixed physical external partition and interaction sizes, the Dyson
sum over actual connected Wick diagrams with the owner shuffle τ equals
the ordered-simplex sum for the reference owner shuffle σ. Local source
labels and exact paired legs are preserved by the owner equivalence;
no individual canonical integral is factorized. -/
theorem ExternalInsertionBlockLayout.sum_ofFamilyShuffle_connectedDyson_eq_referenceOrdered
    {E n : ℕ}
    (π : Finpartition (Finset.univ : Finset (Fin (2 * E))))
    (heven : ∀ B : π.parts, Even (B : Finset (Fin (2 * E))).card)
    {size : π.parts → ℕ}
    (σ τ : Combinatorics.FamilySlotShuffleTo size n)
    (localLabels : ∀ B : π.parts,
      Fin (2 * ((B : Finset (Fin (2 * E))).card / 2)) →
        ExternalFieldLabel Mode)
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) :
    (∑ G : (ExternalInsertionBlockLayout.ofFamilyShuffle π heven τ).ConnectedBlockFamily
        (ExternalLabel := ExternalFieldLabel Mode)
        (InternalLabel := QuarticVertexLabel Mode),
      if ∀ B : π.parts, (G.1 B).externalLabel = localLabels B then
        ExternalInsertionWickDiagram.dysonAmplitude
          ((ExternalInsertionBlockLayout.ofFamilyShuffle π heven τ).assembleDiagram
            (Finset.univ : Finset (Fin n)) G.1)
          ε β g externalTime
      else 0) =
      ∑ F : (ExternalInsertionBlockLayout.ofFamilyShuffle π heven σ).ConnectedBlockFamily
          (ExternalLabel := ExternalFieldLabel Mode)
          (InternalLabel := QuarticVertexLabel Mode),
        if ∀ B : π.parts, (F.1 B).externalLabel = localLabels B then
          ExternalInsertionWickDiagram.orderedDysonAmplitude
            ((ExternalInsertionBlockLayout.ofFamilyShuffle π heven σ).assembleDiagram
              (Finset.univ : Finset (Fin n)) F.1)
            ε β g externalTime
            (((Finset.univ : Finset (Fin n)).orderIsoOfFin rfl).toEquiv.trans
              (fullInteractionSlotEquiv (σ.ambientRelabel τ)).symm)
        else 0 := by
  have h :=
    ExternalInsertionBlockLayout.sum_ownerSlotCongr_connectedDyson_eq_ordered_localLabels
      (ExternalInsertionBlockLayout.ofFamilyShuffle π heven σ)
      (σ.ambientRelabel τ) localLabels ε β hβ g externalTime
  simpa only [ExternalInsertionBlockLayout.ofFamilyShuffle_ownerSlotCongr] using h

open Classical in
/-- The finite canonical Dyson sum over all physical owner shuffles of
fixed realized local sizes is a transported-order orbit on one fixed
reference owner assignment, retaining local source-label conditions,
paired Wick legs, and every zero-interaction block. -/
theorem ExternalInsertionBlockLayout.sum_allOwnerShuffles_connectedDyson_eq_referenceOrdered
    {E n : ℕ}
    (π : Finpartition (Finset.univ : Finset (Fin (2 * E))))
    (heven : ∀ B : π.parts, Even (B : Finset (Fin (2 * E))).card)
    {size : π.parts → ℕ}
    (σ : Combinatorics.FamilySlotShuffleTo size n)
    (localLabels : ∀ B : π.parts,
      Fin (2 * ((B : Finset (Fin (2 * E))).card / 2)) →
        ExternalFieldLabel Mode)
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) :
    (∑ τ : Combinatorics.FamilySlotShuffleTo size n,
      ∑ G : (ExternalInsertionBlockLayout.ofFamilyShuffle π heven τ).ConnectedBlockFamily
          (ExternalLabel := ExternalFieldLabel Mode)
          (InternalLabel := QuarticVertexLabel Mode),
        if ∀ B : π.parts, (G.1 B).externalLabel = localLabels B then
          ExternalInsertionWickDiagram.dysonAmplitude
            ((ExternalInsertionBlockLayout.ofFamilyShuffle π heven τ).assembleDiagram
              (Finset.univ : Finset (Fin n)) G.1)
            ε β g externalTime
        else 0) =
      ∑ τ : Combinatorics.FamilySlotShuffleTo size n,
        ∑ F : (ExternalInsertionBlockLayout.ofFamilyShuffle π heven σ).ConnectedBlockFamily
            (ExternalLabel := ExternalFieldLabel Mode)
            (InternalLabel := QuarticVertexLabel Mode),
          if ∀ B : π.parts, (F.1 B).externalLabel = localLabels B then
            ExternalInsertionWickDiagram.orderedDysonAmplitude
              ((ExternalInsertionBlockLayout.ofFamilyShuffle π heven σ).assembleDiagram
                (Finset.univ : Finset (Fin n)) F.1)
              ε β g externalTime
              (((Finset.univ : Finset (Fin n)).orderIsoOfFin rfl).toEquiv.trans
                (fullInteractionSlotEquiv (σ.ambientRelabel τ)).symm)
          else 0 := by
  apply Finset.sum_congr rfl
  intro τ _
  exact ExternalInsertionBlockLayout.sum_ofFamilyShuffle_connectedDyson_eq_referenceOrdered
    π heven σ τ localLabels ε β hβ g externalTime

end Fermionic
end SecondQuantization
