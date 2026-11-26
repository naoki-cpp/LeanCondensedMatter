import LeanCondensedMatter.Combinatorics.Shuffle.SlotShuffle
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Core.Diagram
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Leg
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.StableTimedEventOrder
import LeanCondensedMatter.Combinatorics.Shuffle.FamilySlotShuffleSign
import LeanCondensedMatter.Combinatorics.Common.ListFlatMapOrder
import Mathlib.Tactic.FinCases
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Basic.Real.Basic

set_option linter.style.header false

/-!
# Imaginary-time event and atomic-leg order for external insertions

This module supplies statistics-independent imaginary-time ordering coordinates for
arbitrary external insertions. It does not assign fermionic exchange signs.

The data are:

* sort the `2 * E` external events together with `n` interaction events by imaginary time;
* expand that event order to the corresponding atomic legs;
* identify the time-ordered atomic positions with the fixed flattened
  `ExternalInsertionDiagram` positions.

Further transport and locality lemmas are intentionally deferred until a concrete amplitude
factorization proof needs them.
-/

namespace SecondQuantization
namespace Common

/-- External and interaction events in the arbitrary-external time-ordered family. -/
abbrev ExternalInsertionTimedEvent (E n : ℕ) : Type :=
  Fin (2 * E) ⊕ Fin n

/-- Imaginary time of an external or interaction event. -/
def externalInsertionTimedEventTime {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    ExternalInsertionTimedEvent E n → ℝ
  | .inl e => externalTime e
  | .inr v => σ v

private def externalInsertionTimedEventRank {E n : ℕ}
    (event : ExternalInsertionTimedEvent E n) : ℕ :=
  ((finSumFinEquiv : ExternalInsertionTimedEvent E n ≃ Fin (2 * E + n)) event).val

private def externalInsertionTimedEventBeforeOrEqual {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (a b : ExternalInsertionTimedEvent E n) : Prop :=
  stableTimedEventBeforeOrEqual
    (externalInsertionTimedEventTime externalTime σ) externalInsertionTimedEventRank a b

private def canonicalExternalInsertionTimedEvents (E n : ℕ) :
    List (ExternalInsertionTimedEvent E n) :=
  List.ofFn fun p : Fin (2 * E + n) =>
    (finSumFinEquiv :
      ExternalInsertionTimedEvent E n ≃ Fin (2 * E + n)).symm p

/-- All external and interaction events sorted by decreasing imaginary time.
Equal-time events use the fixed flattened external-first rank. -/
noncomputable def orderedExternalInsertionTimedEvents {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    List (ExternalInsertionTimedEvent E n) := by
  classical
  exact List.insertionSort
    (externalInsertionTimedEventBeforeOrEqual externalTime σ)
    (canonicalExternalInsertionTimedEvents E n)

private theorem orderedExternalInsertionTimedEvents_perm {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    List.Perm (orderedExternalInsertionTimedEvents externalTime σ)
      (canonicalExternalInsertionTimedEvents E n) := by
  classical
  exact List.perm_insertionSort _ _

/-- Scalar products over the sorted mixed events are independent of their order. -/
theorem prod_orderedExternalInsertionTimedEvents {R : Type*} [CommMonoid R]
    {E n : ℕ} (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (a : ExternalInsertionTimedEvent E n → R) :
    ((orderedExternalInsertionTimedEvents externalTime σ).map a).prod =
      ∏ e : ExternalInsertionTimedEvent E n, a e := by
  classical
  have hprod : ∀ (k : ℕ) (f : Fin k → R),
      (List.ofFn f).prod = ∏ i, f i := by
    intro k
    induction k with
    | zero =>
        intro f
        simp
    | succ k ih =>
        intro f
        rw [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ, ih]
  rw [((orderedExternalInsertionTimedEvents_perm externalTime σ).map a).prod_eq,
    canonicalExternalInsertionTimedEvents, List.map_ofFn, hprod]
  exact Equiv.prod_comp
    (finSumFinEquiv : ExternalInsertionTimedEvent E n ≃ Fin (2 * E + n)).symm a

/-- Stable mixed ordering contains no duplicate events. -/
theorem orderedExternalInsertionTimedEvents_nodup {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    (orderedExternalInsertionTimedEvents externalTime σ).Nodup :=
  (orderedExternalInsertionTimedEvents_perm externalTime σ).nodup_iff.mpr (by
    unfold canonicalExternalInsertionTimedEvents
    exact List.nodup_ofFn_ofInjective
      ((finSumFinEquiv :
        ExternalInsertionTimedEvent E n ≃ Fin (2 * E + n)).symm.injective))

/-- Stable mixed ordering contains every event. -/
theorem orderedExternalInsertionTimedEvents_all_mem {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    ∀ event : ExternalInsertionTimedEvent E n,
      event ∈ orderedExternalInsertionTimedEvents externalTime σ := by
  intro event
  apply (orderedExternalInsertionTimedEvents_perm externalTime σ).symm.subset
  rw [canonicalExternalInsertionTimedEvents, List.mem_ofFn]
  exact ⟨
    (finSumFinEquiv :
      ExternalInsertionTimedEvent E n ≃ Fin (2 * E + n)) event,
    by simp⟩

/-- Stable mixed ordering is pairwise sorted. -/
theorem orderedExternalInsertionTimedEvents_pairwise {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    (orderedExternalInsertionTimedEvents externalTime σ).Pairwise
      (stableTimedEventBeforeOrEqual (externalInsertionTimedEventTime externalTime σ)
        (fun e => (finSumFinEquiv e : Fin (2 * E + n)).val)) := by
  classical
  change
    (List.insertionSort
      (stableTimedEventBeforeOrEqual
        (externalInsertionTimedEventTime externalTime σ)
        externalInsertionTimedEventRank)
      (canonicalExternalInsertionTimedEvents E n)).Pairwise
        (stableTimedEventBeforeOrEqual
          (externalInsertionTimedEventTime externalTime σ)
          externalInsertionTimedEventRank)
  exact List.pairwise_insertionSort _ _

/-- With no external events and strictly decreasing interaction times, the stable
mixed-event sort leaves the canonical interaction-slot order unchanged. -/
private theorem orderedExternalInsertionTimedEvents_zero_eq_canonical_of_strictAnti
    {n : ℕ} (σ : Fin n → ℝ) (hσ : StrictAnti σ) :
    orderedExternalInsertionTimedEvents (E := 0) (Fin.elim0 : Fin 0 → ℝ) σ =
      canonicalExternalInsertionTimedEvents 0 n := by
  classical
  unfold orderedExternalInsertionTimedEvents
  apply List.Pairwise.insertionSort_eq
  rw [canonicalExternalInsertionTimedEvents, List.pairwise_ofFn]
  intro a b hab
  cases ha :
      (finSumFinEquiv : ExternalInsertionTimedEvent 0 n ≃ Fin (0 + n)).symm a with
  | inl i => exact i.elim0
  | inr i =>
    cases hb :
        (finSumFinEquiv : ExternalInsertionTimedEvent 0 n ≃ Fin (0 + n)).symm b with
    | inl j => exact j.elim0
    | inr j =>
      have hai : (i : ℕ) = (a : ℕ) := by
        have h := congrArg Fin.val
          ((finSumFinEquiv : ExternalInsertionTimedEvent 0 n ≃ Fin (0 + n)).apply_symm_apply a)
        rw [ha, finSumFinEquiv_apply_right] at h
        simpa using h
      have hbj : (j : ℕ) = (b : ℕ) := by
        have h := congrArg Fin.val
          ((finSumFinEquiv : ExternalInsertionTimedEvent 0 n ≃ Fin (0 + n)).apply_symm_apply b)
        rw [hb, finSumFinEquiv_apply_right] at h
        simpa using h
      have hij : i < j := Fin.lt_def.mpr (by omega)
      simp only [externalInsertionTimedEventBeforeOrEqual,
        stableTimedEventBeforeOrEqual_iff]
      left
      simpa only [ha, hb, externalInsertionTimedEventTime] using hσ hij

variable {E₁ E₂ m n : ℕ}

private theorem externalInsertionTimedEventTime_map
    (fExternal : Fin (2 * E₁) → Fin (2 * E₂))
    (fInteraction : Fin m → Fin n)
    (externalTime : Fin (2 * E₂) → ℝ) (σ : Fin n → ℝ)
    (event : ExternalInsertionTimedEvent E₁ m) :
    externalInsertionTimedEventTime externalTime σ
        (Sum.map fExternal fInteraction event) =
      externalInsertionTimedEventTime (externalTime ∘ fExternal) (σ ∘ fInteraction) event := by
  cases event <;> rfl

private theorem externalInsertionTimedEventBeforeOrEqual_map_iff
    {fExternal : Fin (2 * E₁) → Fin (2 * E₂)}
    {fInteraction : Fin m → Fin n}
    (hExternal : StrictMono fExternal) (hInteraction : StrictMono fInteraction)
    (externalTime : Fin (2 * E₂) → ℝ) (σ : Fin n → ℝ)
    (a b : ExternalInsertionTimedEvent E₁ m) :
    externalInsertionTimedEventBeforeOrEqual externalTime σ
        (Sum.map fExternal fInteraction a)
        (Sum.map fExternal fInteraction b) ↔
      externalInsertionTimedEventBeforeOrEqual
        (externalTime ∘ fExternal) (σ ∘ fInteraction) a b := by
  simp only [externalInsertionTimedEventBeforeOrEqual, stableTimedEventBeforeOrEqual_iff,
    externalInsertionTimedEventTime_map, externalInsertionTimedEventRank]
  rw [finSumFinEquiv_map_val_le_iff hExternal hInteraction a b]

/-- Increasing external/interaction slot reindexings embed the locally ordered mixed events as a
sublist of the ambient mixed-event order. -/
private theorem orderedExternalInsertionTimedEvents_map_sublist
    {fExternal : Fin (2 * E₁) → Fin (2 * E₂)}
    {fInteraction : Fin m → Fin n}
    (hExternal : StrictMono fExternal) (hInteraction : StrictMono fInteraction)
    (externalTime : Fin (2 * E₂) → ℝ) (σ : Fin n → ℝ) :
    List.Sublist
      ((orderedExternalInsertionTimedEvents
        (externalTime ∘ fExternal) (σ ∘ fInteraction)).map
          (Sum.map fExternal fInteraction))
      (orderedExternalInsertionTimedEvents externalTime σ) := by
  classical
  let localRel :=
    externalInsertionTimedEventBeforeOrEqual
      (externalTime ∘ fExternal) (σ ∘ fInteraction)
  let ambientRel := externalInsertionTimedEventBeforeOrEqual externalTime σ
  have hLocalPairwise :
      (orderedExternalInsertionTimedEvents
        (externalTime ∘ fExternal) (σ ∘ fInteraction)).Pairwise localRel :=
    orderedExternalInsertionTimedEvents_pairwise
      (externalTime ∘ fExternal) (σ ∘ fInteraction)
  have hMappedPairwise :
      ((orderedExternalInsertionTimedEvents
        (externalTime ∘ fExternal) (σ ∘ fInteraction)).map
          (Sum.map fExternal fInteraction)).Pairwise ambientRel := by
    rw [List.pairwise_map]
    exact hLocalPairwise.imp fun {a b} hab =>
      (externalInsertionTimedEventBeforeOrEqual_map_iff
        hExternal hInteraction externalTime σ a b).2 hab
  have hMapInjective :
      Function.Injective (Sum.map fExternal fInteraction) := by
    simpa using
      (Sum.map_injective.mpr ⟨hExternal.injective, hInteraction.injective⟩)
  have hMappedNodup :
      ((orderedExternalInsertionTimedEvents
        (externalTime ∘ fExternal) (σ ∘ fInteraction)).map
          (Sum.map fExternal fInteraction)).Nodup :=
    List.Nodup.map hMapInjective
      (orderedExternalInsertionTimedEvents_nodup
        (externalTime ∘ fExternal) (σ ∘ fInteraction))
  have hSubperm : List.Subperm
      ((orderedExternalInsertionTimedEvents
        (externalTime ∘ fExternal) (σ ∘ fInteraction)).map
          (Sum.map fExternal fInteraction))
      (orderedExternalInsertionTimedEvents externalTime σ) :=
    hMappedNodup.subperm fun event _ =>
      orderedExternalInsertionTimedEvents_all_mem externalTime σ event
  letI : Std.Antisymm ambientRel :=
    ⟨fun _ _ hab hba =>
      stableTimedEventBeforeOrEqual_antisymm
        (externalInsertionTimedEventTime externalTime σ) externalInsertionTimedEventRank
        (by
          intro a b h
          apply (finSumFinEquiv : ExternalInsertionTimedEvent E₂ n ≃ Fin (2 * E₂ + n)).injective
          apply Fin.ext
          exact h)
        hab hba⟩
  have hAmbientPairwise :
      (orderedExternalInsertionTimedEvents externalTime σ).Pairwise ambientRel :=
    orderedExternalInsertionTimedEvents_pairwise externalTime σ
  exact List.sublist_of_subperm_of_pairwise
    (r := ambientRel) hSubperm hMappedPairwise hAmbientPairwise

/-- The standard external-insertion leg type with `n` ordered interaction slots. -/
abbrev OrderedExternalInsertionLeg (E n : ℕ) : Type :=
  ExternalInsertionLeg E (Finset.univ : Finset (Fin n))

/-- Transport a canonical external-insertion leg along reindexings of the external and interaction slots. -/
def orderedExternalInsertionLegMap {E₁ E₂ m n : ℕ}
    (fExternal : Fin (2 * E₁) → Fin (2 * E₂))
    (fInteraction : Fin m → Fin n) :
    OrderedExternalInsertionLeg E₁ m → OrderedExternalInsertionLeg E₂ n :=
  Sum.map fExternal <|
    Prod.map (fun v => ⟨fInteraction v.1, Finset.mem_univ _⟩) id

/-- Atomic legs contributed by one mixed event. -/
def externalInsertionTimedEventAtomicLegs {E n : ℕ} :
    ExternalInsertionTimedEvent E n → List (OrderedExternalInsertionLeg E n)
  | .inl e => [Sum.inl e]
  | .inr v => List.ofFn fun l : Fin 4 =>
      Sum.inr (⟨v, Finset.mem_univ v⟩, l)

private theorem externalInsertionTimedEventAtomicLegs_map
    (fExternal : Fin (2 * E₁) → Fin (2 * E₂))
    (fInteraction : Fin m → Fin n)
    (event : ExternalInsertionTimedEvent E₁ m) :
    externalInsertionTimedEventAtomicLegs (Sum.map fExternal fInteraction event) =
      (externalInsertionTimedEventAtomicLegs event).map
        (orderedExternalInsertionLegMap fExternal fInteraction) := by
  cases event <;> simp [externalInsertionTimedEventAtomicLegs, orderedExternalInsertionLegMap]

/-- Atomic leg identities in mixed-time event order. -/
noncomputable def externalInsertionMixedTimeOrderedAtomicLegs {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    List (OrderedExternalInsertionLeg E n) :=
  (orderedExternalInsertionTimedEvents externalTime σ).flatMap
    externalInsertionTimedEventAtomicLegs

/-- Increasing external/interaction slot reindexings embed the local mixed atomic-leg
order as a sublist of the ambient mixed atomic-leg order. -/
private theorem externalInsertionMixedTimeOrderedAtomicLegs_map_sublist
    {fExternal : Fin (2 * E₁) → Fin (2 * E₂)}
    {fInteraction : Fin m → Fin n}
    (hExternal : StrictMono fExternal) (hInteraction : StrictMono fInteraction)
    (externalTime : Fin (2 * E₂) → ℝ) (σ : Fin n → ℝ) :
    List.Sublist
      ((externalInsertionMixedTimeOrderedAtomicLegs
        (externalTime ∘ fExternal) (σ ∘ fInteraction)).map
          (orderedExternalInsertionLegMap fExternal fInteraction))
      (externalInsertionMixedTimeOrderedAtomicLegs externalTime σ) := by
  have h := (orderedExternalInsertionTimedEvents_map_sublist
    hExternal hInteraction externalTime σ).flatMap externalInsertionTimedEventAtomicLegs
  simpa [externalInsertionMixedTimeOrderedAtomicLegs, List.flatMap_map, List.map_flatMap,
    externalInsertionTimedEventAtomicLegs_map] using h

private theorem externalInsertionTimedEventAtomicLegs_nodup {E n : ℕ}
    (event : ExternalInsertionTimedEvent E n) :
    (externalInsertionTimedEventAtomicLegs event).Nodup := by
  cases event with
  | inl e => simp [externalInsertionTimedEventAtomicLegs]
  | inr v =>
      rw [externalInsertionTimedEventAtomicLegs]
      apply List.nodup_ofFn_ofInjective
      intro a b h
      exact congrArg Prod.snd (Sum.inr.inj h)

private theorem externalInsertionTimedEventAtomicLegs_disjoint {E n : ℕ}
    {a b : ExternalInsertionTimedEvent E n} (h : a ≠ b) :
    List.Disjoint (externalInsertionTimedEventAtomicLegs a)
      (externalInsertionTimedEventAtomicLegs b) := by
  cases a <;> cases b <;>
    simp_all [externalInsertionTimedEventAtomicLegs, ne_comm]

/-- On the strictly ordered vacuum-only time chamber, mixed atomic legs are
listed in the canonical flattened quartic-leg order. -/
private theorem externalInsertionMixedTimeOrderedAtomicLegs_zero_eq_flattened_of_strictAnti
    {n : ℕ} (σ : Fin n → ℝ) (hσ : StrictAnti σ) :
    externalInsertionMixedTimeOrderedAtomicLegs (E := 0)
        (Fin.elim0 : Fin 0 → ℝ) σ =
      List.ofFn (fun q : Fin (2 * (2 * n)) =>
        (Sum.inr
          (⟨(orderedQuarticLegEquiv n q).1, Finset.mem_univ _⟩,
            (orderedQuarticLegEquiv n q).2) : OrderedExternalInsertionLeg 0 n)) := by
  classical
  have hcanonical :
      canonicalExternalInsertionTimedEvents 0 n =
        List.ofFn (fun i : Fin n => (Sum.inr i : ExternalInsertionTimedEvent 0 n)) := by
    unfold canonicalExternalInsertionTimedEvents
    rw [List.ofFn_congr (Nat.zero_add n)]
    apply congrArg List.ofFn
    funext i
    have hcast :
        Fin.cast (Nat.zero_add n).symm i = Fin.natAdd 0 i := by
      apply Fin.ext
      simp
    rw [hcast]
    exact finSumFinEquiv_symm_apply_natAdd i
  unfold externalInsertionMixedTimeOrderedAtomicLegs
  rw [orderedExternalInsertionTimedEvents_zero_eq_canonical_of_strictAnti σ hσ,
    hcanonical]
  have hflat :
      (List.ofFn (fun i : Fin n => (Sum.inr i : ExternalInsertionTimedEvent 0 n))).flatMap
          externalInsertionTimedEventAtomicLegs =
        (List.ofFn (fun i : Fin n =>
          List.ofFn (fun j : Fin 4 =>
            (Sum.inr (⟨i, Finset.mem_univ _⟩, j) :
              OrderedExternalInsertionLeg 0 n)))).flatten := by
    rw [List.flatMap_def, List.map_ofFn]
    rfl
  rw [hflat]
  let g : Fin n → Fin 4 → OrderedExternalInsertionLeg 0 n :=
    fun i j => Sum.inr (⟨i, Finset.mem_univ _⟩, j)
  change (List.ofFn (fun i : Fin n => List.ofFn (g i))).flatten =
    List.ofFn (orderedQuarticLegFamily g)
  have hcard : 2 * (2 * n) = n * 4 := by omega
  rw [List.ofFn_congr hcard (orderedQuarticLegFamily g), List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  change g i j =
    g (orderedQuarticLegEquiv n
      (Fin.cast hcard.symm
        ⟨(i : ℕ) * 4 + (j : ℕ), Combinatorics.FiniteIndex.blockCoordinate_lt i j⟩)).1
      (orderedQuarticLegEquiv n
        (Fin.cast hcard.symm
          ⟨(i : ℕ) * 4 + (j : ℕ), Combinatorics.FiniteIndex.blockCoordinate_lt i j⟩)).2
  exact (congrArg (fun p : Fin n × Fin 4 => g p.1 p.2)
    (Combinatorics.FiniteIndex.blockEquiv_cast_mul_add hcard i j)).symm

/-- The general mixed atomic-leg order has no duplicate identities. -/
theorem externalInsertionMixedTimeOrderedAtomicLegs_nodup {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    (externalInsertionMixedTimeOrderedAtomicLegs externalTime σ).Nodup := by
  rw [externalInsertionMixedTimeOrderedAtomicLegs, List.nodup_flatMap]
  refine ⟨
    fun event _ => externalInsertionTimedEventAtomicLegs_nodup event,
    ?_⟩
  exact
    (orderedExternalInsertionTimedEvents_nodup externalTime σ).pairwise_of_forall_ne
      (fun _ _ _ _ h => externalInsertionTimedEventAtomicLegs_disjoint h)

/-- The general mixed atomic-leg order contains every canonical leg. -/
theorem externalInsertionMixedTimeOrderedAtomicLegs_all_mem {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    ∀ leg : OrderedExternalInsertionLeg E n,
      leg ∈ externalInsertionMixedTimeOrderedAtomicLegs externalTime σ := by
  intro leg
  rw [externalInsertionMixedTimeOrderedAtomicLegs, List.mem_flatMap]
  cases leg with
  | inl e =>
      exact ⟨
        Sum.inl e,
        orderedExternalInsertionTimedEvents_all_mem externalTime σ (Sum.inl e),
        by simp [externalInsertionTimedEventAtomicLegs]⟩
  | inr p =>
      rcases p with ⟨⟨v, hv⟩, l⟩
      refine ⟨
        Sum.inr v,
        orderedExternalInsertionTimedEvents_all_mem externalTime σ (Sum.inr v),
        ?_⟩
      rw [externalInsertionTimedEventAtomicLegs, List.mem_ofFn]
      exact ⟨l, rfl⟩

/-- The general mixed atomic-leg order has one position per canonical leg. -/
theorem externalInsertionMixedTimeOrderedAtomicLegs_length {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    (externalInsertionMixedTimeOrderedAtomicLegs externalTime σ).length =
      2 * (2 * n + E) := by
  let l := externalInsertionMixedTimeOrderedAtomicLegs externalTime σ
  have hcard :
      l.length = Fintype.card (OrderedExternalInsertionLeg E n) := by
    simpa using
      Fintype.card_congr
        (List.Nodup.getEquivOfForallMemList l
          (externalInsertionMixedTimeOrderedAtomicLegs_nodup externalTime σ)
          (externalInsertionMixedTimeOrderedAtomicLegs_all_mem externalTime σ))
  rw [hcard]
  simp [OrderedExternalInsertionLeg]
  omega

/-- Exact bijection from mixed-time atomic positions to canonical external-insertion legs. -/
noncomputable def externalInsertionMixedTimeOrderedAtomicLegEquiv {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    Fin (2 * (2 * n + E)) ≃ OrderedExternalInsertionLeg E n :=
  (finCongr
    (externalInsertionMixedTimeOrderedAtomicLegs_length externalTime σ).symm).trans
    (List.Nodup.getEquivOfForallMemList
      (externalInsertionMixedTimeOrderedAtomicLegs externalTime σ)
      (externalInsertionMixedTimeOrderedAtomicLegs_nodup externalTime σ)
      (externalInsertionMixedTimeOrderedAtomicLegs_all_mem externalTime σ))

/-- The mixed-time atomic leg enumeration agrees with the event-level
flattened list. This is the interface needed to identify products of full
time-ordered vertices with products of their individual atomic fields. -/
theorem externalInsertionMixedTimeOrderedAtomicLegs_eq_ofFn {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    externalInsertionMixedTimeOrderedAtomicLegs externalTime σ =
      List.ofFn (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ) := by
  let legs := externalInsertionMixedTimeOrderedAtomicLegs externalTime σ
  have h : legs.length = 2 * (2 * n + E) :=
    externalInsertionMixedTimeOrderedAtomicLegs_length externalTime σ
  have hlist :
      List.ofFn (fun p : Fin (2 * (2 * n + E)) =>
        legs.get (Fin.cast h.symm p)) = legs := by
    exact (List.ofFn_congr h legs.get).symm.trans (List.ofFn_get legs)
  change legs = List.ofFn (fun p : Fin (2 * (2 * n + E)) =>
    legs.get (Fin.cast h.symm p))
  exact hlist.symm

/-- The mixed position occupied by a canonical external-insertion leg identity. -/
noncomputable def externalInsertionMixedTimeOrderedAtomicLegPosition {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (leg : OrderedExternalInsertionLeg E n) : Fin (2 * (2 * n + E)) :=
  (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ).symm leg

@[simp]
theorem externalInsertionMixedTimeOrderedAtomicLegEquiv_position {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (leg : OrderedExternalInsertionLeg E n) :
    externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ
        (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ leg) = leg :=
  (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ).apply_symm_apply leg

/-- Increasing reindexings of the external and interaction slots embed the local mixed atomic
positions strictly monotonically into the ambient mixed atomic order. -/
theorem externalInsertionMixedTimeOrderedAtomicLegPosition_map_strictMono
    {fExternal : Fin (2 * E₁) → Fin (2 * E₂)}
    {fInteraction : Fin m → Fin n}
    (hExternal : StrictMono fExternal) (hInteraction : StrictMono fInteraction)
    (externalTime : Fin (2 * E₂) → ℝ) (σ : Fin n → ℝ) :
    StrictMono (fun p : Fin (2 * (2 * m + E₁)) =>
      externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
        (orderedExternalInsertionLegMap fExternal fInteraction
          (externalInsertionMixedTimeOrderedAtomicLegEquiv
            (externalTime ∘ fExternal) (σ ∘ fInteraction) p))) := by
  let localLegs :=
    externalInsertionMixedTimeOrderedAtomicLegs
      (externalTime ∘ fExternal) (σ ∘ fInteraction)
  let ambientLegs := externalInsertionMixedTimeOrderedAtomicLegs externalTime σ
  let legMap := orderedExternalInsertionLegMap fExternal fInteraction
  have hSub : (localLegs.map legMap).Sublist ambientLegs := by
    simpa [localLegs, ambientLegs, legMap] using
      (externalInsertionMixedTimeOrderedAtomicLegs_map_sublist
        hExternal hInteraction externalTime σ)
  obtain ⟨positionEmbedding, hget⟩ :=
    List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hSub
  have hLocalLength :
      (localLegs.map legMap).length = 2 * (2 * m + E₁) := by
    simpa [localLegs] using
      (externalInsertionMixedTimeOrderedAtomicLegs_length
        (externalTime ∘ fExternal) (σ ∘ fInteraction))
  have hAmbientLength :
      ambientLegs.length = 2 * (2 * n + E₂) := by
    simpa [ambientLegs] using
      (externalInsertionMixedTimeOrderedAtomicLegs_length externalTime σ)
  have hLocalGet (p : Fin (2 * (2 * m + E₁))) :
      (localLegs.map legMap).get ((Fin.castOrderIso hLocalLength.symm) p) =
        legMap (externalInsertionMixedTimeOrderedAtomicLegEquiv
          (externalTime ∘ fExternal) (σ ∘ fInteraction) p) := by
    simp only [List.get_eq_getElem, List.getElem_map]
    apply congrArg legMap
    change localLegs.get _ = localLegs.get _
    apply congrArg localLegs.get
    apply Fin.ext
    rfl
  have hAmbientGet (p : Fin ambientLegs.length) :
      externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ
          ((Fin.castOrderIso hAmbientLength) p) =
        ambientLegs.get p := by
    change ambientLegs.get _ = ambientLegs.get p
    congr
  have hPosition (p : Fin (2 * (2 * m + E₁))) :
      externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
          (legMap (externalInsertionMixedTimeOrderedAtomicLegEquiv
            (externalTime ∘ fExternal) (σ ∘ fInteraction) p)) =
        (Fin.castOrderIso hAmbientLength)
          (positionEmbedding ((Fin.castOrderIso hLocalLength.symm) p)) := by
    apply (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ).injective
    rw [externalInsertionMixedTimeOrderedAtomicLegEquiv_position, hAmbientGet]
    rw [← hget]
    exact (hLocalGet p).symm
  intro p q hpq
  dsimp only [legMap] at hPosition ⊢
  rw [hPosition p, hPosition q]
  exact (Fin.castOrderIso hAmbientLength).strictMono
    (positionEmbedding.strictMono
      ((Fin.castOrderIso hLocalLength.symm).strictMono hpq))

/-- On an ordered vacuum-only time chamber, the canonical quartic leg order
agrees with mixed-time atomic positions. -/
theorem externalInsertionMixedTimeOrderedAtomicLegPosition_zero_strictMono_of_strictAnti
    {n : ℕ} (σ : Fin n → ℝ) (hσ : StrictAnti σ) :
    StrictMono (fun q : Fin (2 * (2 * n)) =>
      externalInsertionMixedTimeOrderedAtomicLegPosition (E := 0)
        (Fin.elim0 : Fin 0 → ℝ) σ
        (Sum.inr
          (⟨(orderedQuarticLegEquiv n q).1, Finset.mem_univ _⟩,
            (orderedQuarticLegEquiv n q).2))) := by
  let leg (q : Fin (2 * (2 * n))) : OrderedExternalInsertionLeg 0 n :=
    Sum.inr (⟨(orderedQuarticLegEquiv n q).1, Finset.mem_univ _⟩,
      (orderedQuarticLegEquiv n q).2)
  let position (q : Fin (2 * (2 * n))) : Fin (2 * (2 * n + 0)) :=
    externalInsertionMixedTimeOrderedAtomicLegPosition (E := 0)
      (Fin.elim0 : Fin 0 → ℝ) σ (leg q)
  have hlist :=
    externalInsertionMixedTimeOrderedAtomicLegs_zero_eq_flattened_of_strictAnti σ hσ
  have hcard : 2 * (2 * n) = 2 * (2 * n + 0) := by omega
  have hforward (q : Fin (2 * (2 * n))) :
      externalInsertionMixedTimeOrderedAtomicLegEquiv (E := 0)
          (Fin.elim0 : Fin 0 → ℝ) σ (Fin.cast hcard q) = leg q := by
    unfold externalInsertionMixedTimeOrderedAtomicLegEquiv
    simp only [Equiv.trans_apply, List.Nodup.getEquivOfForallMemList_apply,
      finCongr_apply]
    simp [hlist, leg]
  have hposition (q : Fin (2 * (2 * n))) :
      position q = Fin.cast hcard q := by
    apply (externalInsertionMixedTimeOrderedAtomicLegEquiv (E := 0)
      (Fin.elim0 : Fin 0 → ℝ) σ).injective
    rw [externalInsertionMixedTimeOrderedAtomicLegEquiv_position]
    exact (hforward q).symm
  intro p q hpq
  change position p < position q
  simpa only [hposition, Fin.lt_def, Fin.val_cast] using hpq

/-- Permutation from the fixed flattened diagram-leg order to mixed-time atomic positions. -/
noncomputable def externalInsertionStandardToMixedAtomicPositionEquiv {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    Equiv.Perm (Fin (2 * (2 * n + E))) :=
  (finCongr (by simp)).trans
    ((externalInsertionLegEquiv E (Finset.univ : Finset (Fin n))).trans
      (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ).symm)

/-! ## Event-block permutation parity -/

private abbrev externalInsertionEventBlockSize (E n : ℕ) :
    ExternalInsertionTimedEvent E n → ℕ
  | .inl _ => 1
  | .inr _ => 4

private def externalInsertionEventBlockLegEquiv (E n : ℕ) :
    (Σ e : ExternalInsertionTimedEvent E n, Fin (externalInsertionEventBlockSize E n e)) ≃
      OrderedExternalInsertionLeg E n where
  toFun
    | ⟨.inl e, _⟩ => .inl e
    | ⟨.inr v, l⟩ => .inr (⟨v, Finset.mem_univ v⟩, l)
  invFun
    | .inl e => ⟨.inl e, 0⟩
    | .inr (v, l) => ⟨.inr v.1, l⟩
  left_inv := by
    rintro ⟨e, l⟩
    cases e with
    | inl e =>
        have hl : l = 0 := Subsingleton.elim _ _
        subst l
        rfl
    | inr v => rfl
  right_inv := by
    rintro (e | ⟨v, l⟩)
    · rfl
    · rfl

private theorem externalInsertionEventBlockLegEquiv_mem {E n : ℕ}
    (e : ExternalInsertionTimedEvent E n) (p : Fin (externalInsertionEventBlockSize E n e)) :
    externalInsertionEventBlockLegEquiv E n ⟨e, p⟩ ∈
      externalInsertionTimedEventAtomicLegs e := by
  cases e with
  | inl e => simp [externalInsertionEventBlockLegEquiv, externalInsertionTimedEventAtomicLegs]
  | inr v =>
      rw [externalInsertionTimedEventAtomicLegs, List.mem_ofFn]
      exact ⟨p, rfl⟩

private noncomputable def externalInsertionFixedEventSlotEquiv (E n : ℕ) :
    (Σ e : ExternalInsertionTimedEvent E n, Fin (externalInsertionEventBlockSize E n e)) ≃
      Fin (2 * (2 * n + E)) :=
  (externalInsertionEventBlockLegEquiv E n).trans
    ((finCongr (by simp)).trans
      (externalInsertionLegEquiv E (Finset.univ : Finset (Fin n)))).symm

private theorem externalInsertionFixedEventSlotEquiv_inl_val {E n : ℕ}
    (e : Fin (2 * E)) (p : Fin 1) :
    (externalInsertionFixedEventSlotEquiv E n ⟨.inl e, p⟩).val = e.val := by
  change (externalInsertionExternalLeg E (Finset.univ : Finset (Fin n)) e).val = _
  exact externalInsertionExternalLeg_val E _ e

private theorem externalInsertionFixedEventSlotEquiv_inr_val {E n : ℕ}
    (v : Fin n) (p : Fin 4) :
    (externalInsertionFixedEventSlotEquiv E n ⟨.inr v, p⟩).val =
      2 * E + p.val + 4 * v.val := by
  change (externalInsertionInteractionLeg (E := E)
    (⟨v, Finset.mem_univ v⟩ : ↥(Finset.univ : Finset (Fin n))) p).val = _
  rw [externalInsertionInteractionLeg_val]
  rw [Combinatorics.univ_orderIsoOfFin_symm_val]

/-- Both fixed and mixed event orders have singleton external blocks. Only the
quartic-block local monotonicity requires an order-specific proof. -/
private noncomputable def externalInsertionEventShuffle {E n : ℕ}
    (slot : (Σ e : ExternalInsertionTimedEvent E n,
      Fin (externalInsertionEventBlockSize E n e)) ≃ Fin (2 * (2 * n + E)))
    (h : ∀ v : Fin n, StrictMono (fun p : Fin 4 => slot ⟨.inr v, p⟩)) :
    Combinatorics.FamilySlotShuffleTo (externalInsertionEventBlockSize E n)
      (2 * (2 * n + E)) where
  slotEquiv := slot
  strictMono := by
    intro e p q hpq
    cases e with
    | inl e =>
        have heq : q = p := Subsingleton.elim _ _
        subst q
        exact (lt_irrefl _ hpq).elim
    | inr v => exact h v hpq

private noncomputable def externalInsertionFixedEventShuffle (E n : ℕ) :
    Combinatorics.FamilySlotShuffleTo (externalInsertionEventBlockSize E n)
      (2 * (2 * n + E)) :=
  externalInsertionEventShuffle (externalInsertionFixedEventSlotEquiv E n) (by
    intro v p q hpq
    change (externalInsertionFixedEventSlotEquiv E n ⟨.inr v, p⟩).val <
      (externalInsertionFixedEventSlotEquiv E n ⟨.inr v, q⟩).val
    rw [externalInsertionFixedEventSlotEquiv_inr_val,
      externalInsertionFixedEventSlotEquiv_inr_val]
    have h : p.val < q.val := hpq
    omega)

private theorem externalInsertionFixedEventShuffle_lt_iff {E n : ℕ}
    (a b : ExternalInsertionTimedEvent E n) (hab : a ≠ b)
    (p : Fin (externalInsertionEventBlockSize E n a))
    (q : Fin (externalInsertionEventBlockSize E n b)) :
    ((externalInsertionFixedEventShuffle E n).slotEquiv ⟨a, p⟩ <
        (externalInsertionFixedEventShuffle E n).slotEquiv ⟨b, q⟩) ↔
      externalInsertionTimedEventRank a < externalInsertionTimedEventRank b := by
  change (externalInsertionFixedEventSlotEquiv E n ⟨a, p⟩).val <
    (externalInsertionFixedEventSlotEquiv E n ⟨b, q⟩).val ↔ _
  cases a with
  | inl a =>
      cases b with
      | inl b =>
          rw [externalInsertionFixedEventSlotEquiv_inl_val,
            externalInsertionFixedEventSlotEquiv_inl_val]
          simp [externalInsertionTimedEventRank]
      | inr b =>
          rw [externalInsertionFixedEventSlotEquiv_inl_val,
            externalInsertionFixedEventSlotEquiv_inr_val]
          have ha := a.isLt
          simp [externalInsertionTimedEventRank]; omega
  | inr a =>
      cases b with
      | inl b =>
          rw [externalInsertionFixedEventSlotEquiv_inr_val,
            externalInsertionFixedEventSlotEquiv_inl_val]
          have hb := b.isLt
          simp [externalInsertionTimedEventRank]; omega
      | inr b =>
          rw [externalInsertionFixedEventSlotEquiv_inr_val,
            externalInsertionFixedEventSlotEquiv_inr_val]
          have hne : a.val ≠ b.val := fun h => hab (congrArg Sum.inr (Fin.ext h))
          have hp : p.val < 4 := p.isLt
          have hq : q.val < 4 := q.isLt
          simp [externalInsertionTimedEventRank]; omega

private noncomputable def externalInsertionMixedEventSlotEquiv {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    (Σ e : ExternalInsertionTimedEvent E n, Fin (externalInsertionEventBlockSize E n e)) ≃
      Fin (2 * (2 * n + E)) :=
  (externalInsertionEventBlockLegEquiv E n).trans
    (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ).symm

private theorem externalInsertionMixedEventSlotEquiv_val {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (e : ExternalInsertionTimedEvent E n) (p : Fin (externalInsertionEventBlockSize E n e)) :
    (externalInsertionMixedEventSlotEquiv externalTime σ ⟨e, p⟩).val =
      @List.idxOf (OrderedExternalInsertionLeg E n) instBEqOfDecidableEq
        (externalInsertionEventBlockLegEquiv E n ⟨e, p⟩)
        (externalInsertionMixedTimeOrderedAtomicLegs externalTime σ) := by
  classical
  rfl

private noncomputable def externalInsertionMixedEventShuffle {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    Combinatorics.FamilySlotShuffleTo (externalInsertionEventBlockSize E n)
      (2 * (2 * n + E)) :=
  externalInsertionEventShuffle (externalInsertionMixedEventSlotEquiv externalTime σ) (by
    classical
    letI : BEq (OrderedExternalInsertionLeg E n) := instBEqOfDecidableEq
    intro v p q hpq
    change (externalInsertionMixedEventSlotEquiv externalTime σ ⟨.inr v, p⟩).val <
      (externalInsertionMixedEventSlotEquiv externalTime σ ⟨.inr v, q⟩).val
    rw [externalInsertionMixedEventSlotEquiv_val, externalInsertionMixedEventSlotEquiv_val]
    apply (List.idxOf_flatMap_block_lt_iff externalInsertionTimedEventAtomicLegs
      (orderedExternalInsertionTimedEvents externalTime σ) (.inr v) _ _
      (externalInsertionMixedTimeOrderedAtomicLegs_nodup externalTime σ)
      (orderedExternalInsertionTimedEvents_all_mem externalTime σ (.inr v))
      (externalInsertionEventBlockLegEquiv_mem (.inr v) p)
      (externalInsertionEventBlockLegEquiv_mem (.inr v) q)).mpr
    have hlocal (l : Fin 4) :
        (externalInsertionTimedEventAtomicLegs (E := E) (.inr v)).idxOf
          (externalInsertionEventBlockLegEquiv E n ⟨.inr v, l⟩) = l.val := by
      fin_cases l <;> simp [externalInsertionTimedEventAtomicLegs,
        externalInsertionEventBlockLegEquiv]
    rw [hlocal, hlocal]
    exact hpq)

private theorem externalInsertionMixedEventShuffle_lt_iff {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (a b : ExternalInsertionTimedEvent E n) (hab : a ≠ b)
    (p : Fin (externalInsertionEventBlockSize E n a))
    (q : Fin (externalInsertionEventBlockSize E n b)) :
    ((externalInsertionMixedEventShuffle externalTime σ).slotEquiv ⟨a, p⟩ <
        (externalInsertionMixedEventShuffle externalTime σ).slotEquiv ⟨b, q⟩) ↔
      @List.idxOf (ExternalInsertionTimedEvent E n) instBEqOfDecidableEq
          a (orderedExternalInsertionTimedEvents externalTime σ) <
        @List.idxOf (ExternalInsertionTimedEvent E n) instBEqOfDecidableEq
          b (orderedExternalInsertionTimedEvents externalTime σ) := by
  classical
  letI : BEq (ExternalInsertionTimedEvent E n) := instBEqOfDecidableEq
  letI : BEq (OrderedExternalInsertionLeg E n) := instBEqOfDecidableEq
  change (externalInsertionMixedEventSlotEquiv externalTime σ ⟨a, p⟩).val <
    (externalInsertionMixedEventSlotEquiv externalTime σ ⟨b, q⟩).val ↔ _
  rw [externalInsertionMixedEventSlotEquiv_val, externalInsertionMixedEventSlotEquiv_val]
  exact List.idxOf_flatMap_lt_iff_idxOf_lt externalInsertionTimedEventAtomicLegs
    (orderedExternalInsertionTimedEvents externalTime σ) a b _ _
    (externalInsertionMixedTimeOrderedAtomicLegs_nodup externalTime σ)
    (orderedExternalInsertionTimedEvents_all_mem externalTime σ a)
    (orderedExternalInsertionTimedEvents_all_mem externalTime σ b)
    (externalInsertionEventBlockLegEquiv_mem a p)
    (externalInsertionEventBlockLegEquiv_mem b q) hab

/-- The full mixed atomic permutation has the sign of the inversions among
the one-legged external events alone. Interactions contribute four consecutive
legs each, so every inversion involving an interaction block is even. This
holds for every time assignment, including ties. -/
theorem externalInsertionStandardToMixedAtomicPositionEquiv_sign
    {E n : ℕ} (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    Equiv.Perm.sign (externalInsertionStandardToMixedAtomicPositionEquiv externalTime σ) =
      (-1 : ℤˣ) ^ (∑ a : Fin (2 * E), ∑ b : Fin (2 * E),
        if a.val < b.val ∧ externalTime a < externalTime b then 1 else 0) := by
  classical
  letI : BEq (ExternalInsertionTimedEvent E n) := instBEqOfDecidableEq
  let f := externalInsertionFixedEventShuffle E n
  let m := externalInsertionMixedEventShuffle externalTime σ
  have hrel : f.relativePerm m =
      externalInsertionStandardToMixedAtomicPositionEquiv externalTime σ := by
    apply Equiv.ext
    intro i
    simp [f, m, Combinatorics.FamilySlotShuffleTo.relativePerm,
      externalInsertionFixedEventShuffle, externalInsertionMixedEventShuffle,
      externalInsertionEventShuffle, externalInsertionFixedEventSlotEquiv, externalInsertionMixedEventSlotEquiv,
      externalInsertionStandardToMixedAtomicPositionEquiv, Equiv.trans_apply]
    rfl
  rw [← hrel, Combinatorics.FamilySlotShuffleTo.relativePerm_sign_eq_oddBlockInversions
    f m externalInsertionTimedEventRank
    (fun e => (orderedExternalInsertionTimedEvents externalTime σ).idxOf e)
    externalInsertionFixedEventShuffle_lt_iff
    (externalInsertionMixedEventShuffle_lt_iff externalTime σ)]
  congr 1
  simp_rw [Fintype.sum_sum_type]
  simp only [externalInsertionEventBlockSize, Nat.reduceMod, Nat.mul_one, Nat.mul_zero,
    ite_self, Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases hab : a.val < b.val
  · have hne : (Sum.inl b : ExternalInsertionTimedEvent E n) ≠ Sum.inl a :=
      fun h => (ne_of_lt hab) (congrArg Fin.val (Sum.inl.inj h).symm)
    letI : Std.Antisymm
        (stableTimedEventBeforeOrEqual (externalInsertionTimedEventTime externalTime σ)
          (fun e => (finSumFinEquiv e : Fin (2 * E + n)).val)) :=
      ⟨fun _ _ h₁ h₂ => stableTimedEventBeforeOrEqual_antisymm _ _
        (fun _ _ h => finSumFinEquiv.injective (Fin.ext h)) h₁ h₂⟩
    have hidx := (orderedExternalInsertionTimedEvents_pairwise externalTime σ).idxOf_lt_iff_of_ne
      (orderedExternalInsertionTimedEvents_all_mem externalTime σ (.inl b))
      (orderedExternalInsertionTimedEvents_all_mem externalTime σ (.inl a)) hne
    have hnot : ¬ b.val ≤ a.val := not_le_of_gt hab
    have htime :
        (orderedExternalInsertionTimedEvents externalTime σ).idxOf (.inl b) <
          (orderedExternalInsertionTimedEvents externalTime σ).idxOf (.inl a) ↔
          externalTime a < externalTime b := by
      rw [hidx, stableTimedEventBeforeOrEqual_iff]
      simp [externalInsertionTimedEventTime, hnot]
    simp [externalInsertionTimedEventRank, hab, htime]
  · simp [externalInsertionTimedEventRank, hab]

/-- The fixed flattened diagram position underlying a mixed-time atomic position. -/
noncomputable def externalInsertionMixedTimeAmbientPositionEquiv {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    Fin (2 * (2 * n + E)) ≃
      Fin (2 * (2 * (Finset.univ : Finset (Fin n)).card + E)) :=
  (externalInsertionStandardToMixedAtomicPositionEquiv externalTime σ).symm.trans
    (finCongr (by simp))

/-- Unflattening the fixed ambient position underlying a mixed position recovers the canonical leg
identity stored at that mixed position. -/
theorem externalInsertionLegEquiv_mixedTimeAmbientPositionEquiv {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (p : Fin (2 * (2 * n + E))) :
    externalInsertionLegEquiv E (Finset.univ : Finset (Fin n))
        (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ p) =
      externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ p := by
  unfold externalInsertionMixedTimeAmbientPositionEquiv
    externalInsertionStandardToMixedAtomicPositionEquiv
  rw [← (externalInsertionLegEquiv E (Finset.univ : Finset (Fin n))).apply_symm_apply
    (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ p)]
  apply congrArg (externalInsertionLegEquiv E (Finset.univ : Finset (Fin n)))
  apply Fin.ext
  rfl


/-- Converting the mixed position of a canonical leg back to fixed order recovers
its flattened diagram position. -/
theorem externalInsertionMixedTimeAmbientPositionEquiv_legPosition {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (leg : OrderedExternalInsertionLeg E n) :
    externalInsertionMixedTimeAmbientPositionEquiv externalTime σ
        (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ leg) =
      (externalInsertionLegEquiv E (Finset.univ : Finset (Fin n))).symm leg := by
  apply (externalInsertionLegEquiv E (Finset.univ : Finset (Fin n))).injective
  rw [externalInsertionLegEquiv_mixedTimeAmbientPositionEquiv,
    externalInsertionMixedTimeOrderedAtomicLegEquiv_position, Equiv.apply_symm_apply]

/-- The canonical mixed atomic-leg enumeration is unchanged if every strict comparison
between external and interaction event times is unchanged. The fixed rank also resolves
all equal-time ties identically. -/
theorem externalInsertionMixedTimeOrderedAtomicLegEquiv_eq_of_comparisons
    {E n : ℕ} (externalTime : Fin (2 * E) → ℝ)
    (σ υ : Fin n → ℝ)
    (h : ∀ a b : ExternalInsertionTimedEvent E n,
      (externalInsertionTimedEventTime externalTime σ a <
        externalInsertionTimedEventTime externalTime σ b) ↔
      (externalInsertionTimedEventTime externalTime υ a <
        externalInsertionTimedEventTime externalTime υ b)) :
    externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ =
      externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime υ := by
  have hrel :
      externalInsertionTimedEventBeforeOrEqual externalTime σ =
        externalInsertionTimedEventBeforeOrEqual externalTime υ := by
    funext a b
    apply propext
    exact stableTimedEventBeforeOrEqual_congr
      (externalInsertionTimedEventTime externalTime σ)
      (externalInsertionTimedEventTime externalTime υ)
      externalInsertionTimedEventRank h a b
  have hordered :
      orderedExternalInsertionTimedEvents externalTime σ =
        orderedExternalInsertionTimedEvents externalTime υ := by
    unfold orderedExternalInsertionTimedEvents
    rw [hrel]
  have hlegs :
      externalInsertionMixedTimeOrderedAtomicLegs externalTime σ =
        externalInsertionMixedTimeOrderedAtomicLegs externalTime υ :=
    congrArg (List.flatMap (externalInsertionTimedEventAtomicLegs (E := E) (n := n))) hordered
  apply Equiv.ext
  intro i
  unfold externalInsertionMixedTimeOrderedAtomicLegEquiv
  simp only [Equiv.trans_apply, List.Nodup.getEquivOfForallMemList_apply,
    List.get_eq_getElem, hlegs]
  rfl


/-- Relabeling interaction events by an arbitrary permutation preserves the
*stable* mixed-time comparison whenever distinct interaction vertices have
distinct times. External times may coincide with one another or with an
interaction time: the external-first tie-breaking rule is unaffected.

This is stronger than requiring all mixed-event times to be pairwise
distinct, and is exactly the property of a strict ordered Dyson chamber. -/
theorem externalInsertionTimedEventBeforeOrEqual_perm_iff
    {E n : ℕ} (externalTime : Fin (2 * E) → ℝ)
    (σ : Fin n → ℝ) (hσ : Function.Injective σ)
    (p : Equiv.Perm (Fin n))
    (a b : ExternalInsertionTimedEvent E n) :
    externalInsertionTimedEventBeforeOrEqual externalTime (σ ∘ p.symm)
        (Sum.map id p a) (Sum.map id p b) ↔
      externalInsertionTimedEventBeforeOrEqual externalTime σ a b := by
  have htime (event : ExternalInsertionTimedEvent E n) :
      externalInsertionTimedEventTime externalTime (σ ∘ p.symm)
          (Sum.map id p event) =
        externalInsertionTimedEventTime externalTime σ event := by
    cases event <;>
      simp [externalInsertionTimedEventTime]
  have hrank (a b : ExternalInsertionTimedEvent E n)
      (ht : externalInsertionTimedEventTime externalTime σ a =
        externalInsertionTimedEventTime externalTime σ b) :
      (externalInsertionTimedEventRank (Sum.map id p a) ≤
        externalInsertionTimedEventRank (Sum.map id p b)) ↔
      (externalInsertionTimedEventRank a ≤
        externalInsertionTimedEventRank b) := by
    cases a with
    | inl i =>
        cases b with
        | inl j => simp [externalInsertionTimedEventRank]
        | inr j =>
            have hi := i.isLt
            have hj := j.isLt
            have hpj := (p j).isLt
            simp [externalInsertionTimedEventRank]; omega
    | inr i =>
        cases b with
        | inl j =>
            have hj := j.isLt
            have hi := i.isLt
            have hpi := (p i).isLt
            simp [externalInsertionTimedEventRank]; omega
        | inr j =>
            have hij : i = j := hσ (by simpa [externalInsertionTimedEventTime] using ht)
            subst j
            simp
  simp only [externalInsertionTimedEventBeforeOrEqual,
    stableTimedEventBeforeOrEqual_iff, htime]
  constructor
  · rintro (h | ⟨ht, hr⟩)
    · exact Or.inl h
    · exact Or.inr ⟨ht, (hrank a b ht).mp hr⟩
  · rintro (h | ⟨ht, hr⟩)
    · exact Or.inl h
    · exact Or.inr ⟨ht, (hrank a b ht).mpr hr⟩


/-- The *whole sorted event list* is transported by any interaction-slot
permutation, provided the interaction times are injective. Equal-time
external insertions remain allowed, including coincidences with vertices.
The proof uses pairwise sortedness and uniqueness of a fully enumerated
finite list, not an assumption about insertion sort implementation. -/
theorem orderedExternalInsertionTimedEvents_perm_slots
    {E n : ℕ} (externalTime : Fin (2 * E) → ℝ)
    (σ : Fin n → ℝ) (hσ : Function.Injective σ)
    (p : Equiv.Perm (Fin n)) :
    (orderedExternalInsertionTimedEvents externalTime σ).map (Sum.map id p) =
      orderedExternalInsertionTimedEvents externalTime (σ ∘ p.symm) := by
  classical
  let source := orderedExternalInsertionTimedEvents externalTime σ
  let target := orderedExternalInsertionTimedEvents externalTime (σ ∘ p.symm)
  let f : ExternalInsertionTimedEvent E n → ExternalInsertionTimedEvent E n :=
    Sum.map id p
  let rel :=
    externalInsertionTimedEventBeforeOrEqual externalTime (σ ∘ p.symm)
  have hPairwise : (source.map f).Pairwise rel := by
    rw [List.pairwise_map]
    exact (orderedExternalInsertionTimedEvents_pairwise externalTime σ).imp
      (fun {a b} hab =>
        (externalInsertionTimedEventBeforeOrEqual_perm_iff externalTime σ hσ p a b).2 hab)
  have hInj : Function.Injective f := by
    exact Sum.map_injective.mpr ⟨Function.injective_id, p.injective⟩
  have hNodup : (source.map f).Nodup :=
    List.Nodup.map hInj (orderedExternalInsertionTimedEvents_nodup externalTime σ)
  have hSubperm : List.Subperm (source.map f) target :=
    hNodup.subperm (fun event _ =>
      orderedExternalInsertionTimedEvents_all_mem externalTime (σ ∘ p.symm) event)
  letI : Std.Antisymm rel :=
    ⟨fun _ _ hab hba =>
      stableTimedEventBeforeOrEqual_antisymm
        (externalInsertionTimedEventTime externalTime (σ ∘ p.symm))
        externalInsertionTimedEventRank
        (by
          intro a b h
          apply (finSumFinEquiv :
            ExternalInsertionTimedEvent E n ≃ Fin (2 * E + n)).injective
          apply Fin.ext
          exact h)
        hab hba⟩
  have hTargetPairwise : target.Pairwise rel :=
    orderedExternalInsertionTimedEvents_pairwise externalTime (σ ∘ p.symm)
  have hSub : (source.map f).Sublist target :=
    List.sublist_of_subperm_of_pairwise
      (r := rel) hSubperm hPairwise hTargetPairwise
  have hLen : (source.map f).length = target.length := by
    simp only [List.length_map]
    exact (orderedExternalInsertionTimedEvents_perm externalTime σ).length_eq.trans
      (orderedExternalInsertionTimedEvents_perm externalTime (σ ∘ p.symm)).length_eq.symm
  exact hSub.eq_of_length hLen


/-- On injective interaction-time assignments, the entire *mixed-time
atomic leg list* is relabeled pointwise by the vertex permutation.
The four atomic legs within each vertex remain consecutive and retain
their local order. This includes external-time coincidences. -/
theorem externalInsertionMixedTimeOrderedAtomicLegs_perm_slots
    {E n : ℕ} (externalTime : Fin (2 * E) → ℝ)
    (σ : Fin n → ℝ) (hσ : Function.Injective σ)
    (p : Equiv.Perm (Fin n)) :
    (externalInsertionMixedTimeOrderedAtomicLegs externalTime σ).map
        (orderedExternalInsertionLegMap id p) =
      externalInsertionMixedTimeOrderedAtomicLegs externalTime (σ ∘ p.symm) := by
  calc
    _ =
        ((orderedExternalInsertionTimedEvents externalTime σ).map
          (Sum.map id p)).flatMap externalInsertionTimedEventAtomicLegs := by
      simp only [externalInsertionMixedTimeOrderedAtomicLegs,
        List.map_flatMap, List.flatMap_map, externalInsertionTimedEventAtomicLegs_map]
    _ = _ := by
      rw [orderedExternalInsertionTimedEvents_perm_slots externalTime σ hσ p]
      rfl


/-- Pointwise covariance of the **actual** mixed-time position-to-leg
equivalence. Every position retains the same physical field under
relabeling, with its vertex identifier renamed by `p`. -/
theorem externalInsertionMixedTimeOrderedAtomicLegEquiv_perm_slots
    {E n : ℕ} (externalTime : Fin (2 * E) → ℝ)
    (σ : Fin n → ℝ) (hσ : Function.Injective σ)
    (p : Equiv.Perm (Fin n))
    (i : Fin (2 * (2 * n + E))) :
    externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime (σ ∘ p.symm) i =
      orderedExternalInsertionLegMap id p
        (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ i) := by
  have hlist :
      List.ofFn (fun i : Fin (2 * (2 * n + E)) =>
        orderedExternalInsertionLegMap id p
          (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ i)) =
      List.ofFn (externalInsertionMixedTimeOrderedAtomicLegEquiv
        externalTime (σ ∘ p.symm)) := by
    simpa only [externalInsertionMixedTimeOrderedAtomicLegs_eq_ofFn,
      List.map_ofFn, Function.comp_def] using
        (externalInsertionMixedTimeOrderedAtomicLegs_perm_slots externalTime σ hσ p)
  exact (congrFun (List.ofFn_injective hlist) i).symm

/-! ## Two even bilinear insertions

The two elementary legs of each bilinear share a time. Stable ordering keeps
them adjacent, with their internal order unchanged, even when an interaction
vertex has the same time. The four-field order is obtained by expanding the
two composite events, not by treating a bilinear as an odd field.
-/

/-- The four external times of two bilinears in fixed creation-annihilation order. -/
def pairedExternalTimes (τ τ' : ℝ) : Fin 4 → ℝ :=
  fun e => if e.val < 2 then τ else τ'

/-- Expand a composite external event into its two fixed elementary events;
interaction events remain single full quartic vertices. -/
def pairedExternalEventBlock {n : ℕ} :
    ExternalInsertionTimedEvent 1 n → List (ExternalInsertionTimedEvent 2 n)
  | .inl e => if e = 0 then [.inl 0, .inl 1] else [.inl 2, .inl 3]
  | .inr v => [.inr v]

/-- Sorting two even composite insertions and then expanding their internal
legs gives exactly the canonical four-field stable event order. -/
theorem orderedExternalInsertionTimedEvents_paired {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    orderedExternalInsertionTimedEvents (E := 2) (pairedExternalTimes τ τ') σ =
      (orderedExternalInsertionTimedEvents (E := 1)
        (fun e => if e = 0 then τ else τ') σ).flatMap pairedExternalEventBlock := by
  classical
  let times : Fin 2 → ℝ := fun e => if e = 0 then τ else τ'
  let source := orderedExternalInsertionTimedEvents (E := 1) times σ
  let target := orderedExternalInsertionTimedEvents (E := 2) (pairedExternalTimes τ τ') σ
  let r₁ := externalInsertionTimedEventBeforeOrEqual (E := 1) times σ
  let r₂ := externalInsertionTimedEventBeforeOrEqual (E := 2) (pairedExternalTimes τ τ') σ
  let block := @pairedExternalEventBlock n
  have hs : source.Pairwise r₁ := orderedExternalInsertionTimedEvents_pairwise (E := 1) times σ
  have hn : source.Nodup := orderedExternalInsertionTimedEvents_nodup (E := 1) times σ
  have ht : target.Pairwise r₂ :=
    orderedExternalInsertionTimedEvents_pairwise (E := 2) (pairedExternalTimes τ τ') σ
  have hblock (a : ExternalInsertionTimedEvent 1 n) : (block a).Nodup := by
    cases a with
    | inl e => fin_cases e <;> simp [block, pairedExternalEventBlock]
    | inr v => simp [block, pairedExternalEventBlock]
  have hdisjoint (a b : ExternalInsertionTimedEvent 1 n) (hne : a ≠ b) :
      List.Disjoint (block a) (block b) := by
    intro x hx hy
    cases a with
    | inl a =>
        cases b with
        | inl b =>
            fin_cases a <;> fin_cases b <;>
              simp_all [block, pairedExternalEventBlock] <;>
              (rcases hx with rfl | rfl) <;> simp_all
        | inr b =>
            fin_cases a <;> simp_all [block, pairedExternalEventBlock]
    | inr a =>
        cases b with
        | inl b =>
            fin_cases b <;> simp_all [block, pairedExternalEventBlock]
        | inr b => simp_all [block, pairedExternalEventBlock]
  have hwithin (a : ExternalInsertionTimedEvent 1 n) :
      (block a).Pairwise r₂ := by
    cases a with
    | inl e =>
        fin_cases e <;>
          simp [block, pairedExternalEventBlock, r₂,
            externalInsertionTimedEventBeforeOrEqual, stableTimedEventBeforeOrEqual_iff,
            externalInsertionTimedEventTime, externalInsertionTimedEventRank, pairedExternalTimes]
    | inr v => simp [block, pairedExternalEventBlock]
  have hcross (a b : ExternalInsertionTimedEvent 1 n) (hne : a ≠ b)
      (hab : r₁ a b) (x y : ExternalInsertionTimedEvent 2 n)
      (hx : x ∈ block a) (hy : y ∈ block b) : r₂ x y := by
    cases a with
    | inl a =>
        cases b with
        | inl b =>
            fin_cases a <;> fin_cases b <;>
              simp_all [block, pairedExternalEventBlock, r₁, r₂, times,
                externalInsertionTimedEventBeforeOrEqual, stableTimedEventBeforeOrEqual_iff,
                externalInsertionTimedEventTime, externalInsertionTimedEventRank,
                pairedExternalTimes] <;>
              (first | omega | aesop (add safe tactic (by omega)))
        | inr b =>
            fin_cases a <;>
              simp_all [block, pairedExternalEventBlock, r₁, r₂, times,
                externalInsertionTimedEventBeforeOrEqual, stableTimedEventBeforeOrEqual_iff,
                externalInsertionTimedEventTime, externalInsertionTimedEventRank,
                pairedExternalTimes] <;>
              (first | omega | aesop (add safe tactic (by omega)))
    | inr a =>
        cases b with
        | inl b =>
            fin_cases b <;>
              simp_all [block, pairedExternalEventBlock, r₁, r₂, times,
                externalInsertionTimedEventBeforeOrEqual, stableTimedEventBeforeOrEqual_iff,
                externalInsertionTimedEventTime, externalInsertionTimedEventRank,
                pairedExternalTimes] <;>
              (first | omega | aesop (add safe tactic (by omega)))
        | inr b =>
            simp_all [block, pairedExternalEventBlock, r₁, r₂,
              externalInsertionTimedEventBeforeOrEqual, stableTimedEventBeforeOrEqual_iff,
              externalInsertionTimedEventTime, externalInsertionTimedEventRank]
  have hsorted (L : List (ExternalInsertionTimedEvent 1 n))
      (hL : L.Pairwise r₁) (hN : L.Nodup) : (L.flatMap block).Pairwise r₂ := by
    induction L with
    | nil => simp
    | cons a L ih =>
        rw [List.flatMap_cons, List.pairwise_append]
        refine ⟨hwithin a, ih (List.pairwise_cons.mp hL).2 (List.nodup_cons.mp hN).2, ?_⟩
        intro x hx y hy
        obtain ⟨b, hb, hyb⟩ := List.mem_flatMap.mp hy
        exact hcross a b (fun he => (List.nodup_cons.mp hN).1 (by simpa [he] using hb))
          ((List.pairwise_cons.mp hL).1 b hb) x y hx hyb
  have hflatN : (source.flatMap block).Nodup := by
    rw [List.nodup_flatMap]
    exact ⟨fun a _ => hblock a,
      hn.pairwise_of_forall_ne (fun _ _ _ _ hne => hdisjoint _ _ hne)⟩
  have hall (x : ExternalInsertionTimedEvent 2 n) : x ∈ source.flatMap block := by
    rw [List.mem_flatMap]
    cases x with
    | inl e =>
        fin_cases e
        · exact ⟨.inl 0, orderedExternalInsertionTimedEvents_all_mem (E := 1) times σ _, by simp [block, pairedExternalEventBlock]⟩
        · exact ⟨.inl 0, orderedExternalInsertionTimedEvents_all_mem (E := 1) times σ _, by simp [block, pairedExternalEventBlock]⟩
        · exact ⟨.inl 1, orderedExternalInsertionTimedEvents_all_mem (E := 1) times σ _, by simp [block, pairedExternalEventBlock]⟩
        · exact ⟨.inl 1, orderedExternalInsertionTimedEvents_all_mem (E := 1) times σ _, by simp [block, pairedExternalEventBlock]⟩
    | inr v =>
        exact ⟨.inr v, orderedExternalInsertionTimedEvents_all_mem (E := 1) times σ _, by simp [block, pairedExternalEventBlock]⟩
  letI : Std.Antisymm r₂ :=
    ⟨fun _ _ hab hba =>
      stableTimedEventBeforeOrEqual_antisymm
        (externalInsertionTimedEventTime (E := 2) (pairedExternalTimes τ τ') σ)
        externalInsertionTimedEventRank
        (by
          intro a b h
          apply (finSumFinEquiv : ExternalInsertionTimedEvent 2 n ≃ Fin (4 + n)).injective
          exact Fin.ext h)
        hab hba⟩
  have hsub : List.Subperm target (source.flatMap block) :=
    (orderedExternalInsertionTimedEvents_nodup (E := 2) (pairedExternalTimes τ τ') σ).subperm
      (fun x _ => hall x)
  have hrev : List.Subperm (source.flatMap block) target :=
    hflatN.subperm (fun x _ =>
      orderedExternalInsertionTimedEvents_all_mem (E := 2) (pairedExternalTimes τ τ') σ x)
  have hlist := List.sublist_of_subperm_of_pairwise (r := r₂)
    hsub ht (hsorted source hs hn)
  exact hlist.eq_of_length (le_antisymm hlist.length_le hrev.length_le)

/-- Exchanging two bilinear blocks has four odd-leg inversions and therefore
no fermionic exchange sign, including at equal times. -/
theorem externalInsertionStandardToMixedAtomicPositionEquiv_sign_paired
    {n : ℕ} (τ τ' : ℝ) (σ : Fin n → ℝ) :
    Equiv.Perm.sign (externalInsertionStandardToMixedAtomicPositionEquiv
      (E := 2) (pairedExternalTimes τ τ') σ) = 1 := by
  classical
  rw [externalInsertionStandardToMixedAtomicPositionEquiv_sign]
  change (-1 : ℤˣ) ^ (∑ a : Fin 4, ∑ b : Fin 4,
    if a.val < b.val ∧ pairedExternalTimes τ τ' a < pairedExternalTimes τ τ' b
    then 1 else 0) = _
  simp only [Fin.sum_univ_four]
  by_cases h : τ < τ'
  · simpa [pairedExternalTimes, h] using (show (-1 : ℤˣ) ^ 4 = 1 by decide)
  · simp [pairedExternalTimes, h]

end Common
end SecondQuantization
