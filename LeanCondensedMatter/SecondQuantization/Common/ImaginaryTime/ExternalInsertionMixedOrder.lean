import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Core.Diagram
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.StableTimedEventOrder
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Basic.Real.Basic

set_option linter.style.header false

/-!
# Mixed-time order for arbitrary external insertions

This module provides only the ordering data needed by the higher-point fermionic consumer:

* sort the `2 * E` external events together with `n` interaction events by imaginary time;
* expand that event order to the corresponding atomic legs;
* identify the time-ordered atomic positions with the fixed flattened
  `ExternalInsertionDiagram` positions.

Further transport and locality lemmas are intentionally deferred until a concrete amplitude
factorization proof needs them.
-/

namespace SecondQuantization
namespace Common

/-- Timed events for `2 * E` external insertions and `n` interaction vertices. -/
private abbrev ExternalInsertionTimedEvent (E n : ℕ) : Type :=
  Fin (2 * E) ⊕ Fin n

/-- The imaginary time carried by an external or interaction event. -/
private def externalInsertionTimedEventTime {E n : ℕ}
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

private theorem canonicalExternalInsertionTimedEvents_nodup (E n : ℕ) :
    (canonicalExternalInsertionTimedEvents E n).Nodup := by
  unfold canonicalExternalInsertionTimedEvents
  exact List.nodup_ofFn_ofInjective
    ((finSumFinEquiv :
      ExternalInsertionTimedEvent E n ≃ Fin (2 * E + n)).symm.injective)

private theorem canonicalExternalInsertionTimedEvents_all_mem (E n : ℕ) :
    ∀ event : ExternalInsertionTimedEvent E n,
      event ∈ canonicalExternalInsertionTimedEvents E n := by
  intro event
  rw [canonicalExternalInsertionTimedEvents, List.mem_ofFn]
  exact ⟨
    (finSumFinEquiv :
      ExternalInsertionTimedEvent E n ≃ Fin (2 * E + n)) event,
    by simp⟩

/-- All external and interaction events sorted by decreasing imaginary time.
Equal-time events use the fixed flattened external-first rank. -/
private noncomputable def orderedExternalInsertionTimedEvents {E n : ℕ}
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

private theorem orderedExternalInsertionTimedEvents_nodup {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    (orderedExternalInsertionTimedEvents externalTime σ).Nodup :=
  (orderedExternalInsertionTimedEvents_perm externalTime σ).nodup_iff.mpr
    (canonicalExternalInsertionTimedEvents_nodup E n)

private theorem orderedExternalInsertionTimedEvents_all_mem {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    ∀ event : ExternalInsertionTimedEvent E n,
      event ∈ orderedExternalInsertionTimedEvents externalTime σ := by
  intro event
  exact (orderedExternalInsertionTimedEvents_perm externalTime σ).symm.subset
    (canonicalExternalInsertionTimedEvents_all_mem E n event)

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
  simp only [externalInsertionTimedEventBeforeOrEqual, stableTimedEventBeforeOrEqual,
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
        (externalTime ∘ fExternal) (σ ∘ fInteraction)).Pairwise localRel := by
    letI : Std.Total localRel :=
      ⟨fun a b =>
        stableTimedEventBeforeOrEqual_total
          (externalInsertionTimedEventTime
            (externalTime ∘ fExternal) (σ ∘ fInteraction))
          externalInsertionTimedEventRank a b⟩
    letI : IsTrans (ExternalInsertionTimedEvent E₁ m) localRel :=
      ⟨fun a b c hab hbc =>
        stableTimedEventBeforeOrEqual_trans
          (externalInsertionTimedEventTime
            (externalTime ∘ fExternal) (σ ∘ fInteraction))
          externalInsertionTimedEventRank hab hbc⟩
    exact List.pairwise_insertionSort _ _
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
      (canonicalExternalInsertionTimedEvents E₂ n) :=
    hMappedNodup.subperm fun event _ =>
      canonicalExternalInsertionTimedEvents_all_mem E₂ n event
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
  letI : Std.Total ambientRel :=
    ⟨fun a b =>
      stableTimedEventBeforeOrEqual_total
        (externalInsertionTimedEventTime externalTime σ) externalInsertionTimedEventRank a b⟩
  letI : IsTrans (ExternalInsertionTimedEvent E₂ n) ambientRel :=
    ⟨fun a b c hab hbc =>
      stableTimedEventBeforeOrEqual_trans
        (externalInsertionTimedEventTime externalTime σ) externalInsertionTimedEventRank hab hbc⟩
  simpa [orderedExternalInsertionTimedEvents, ambientRel] using
    (List.sublist_insertionSort' (r := ambientRel) hMappedPairwise hSubperm)

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

@[simp]
theorem orderedExternalInsertionLegMap_inl {E₁ E₂ m n : ℕ}
    (fExternal : Fin (2 * E₁) → Fin (2 * E₂)) (fInteraction : Fin m → Fin n)
    (e : Fin (2 * E₁)) :
    orderedExternalInsertionLegMap fExternal fInteraction (Sum.inl e) =
      Sum.inl (fExternal e) := rfl

@[simp]
theorem orderedExternalInsertionLegMap_inr {E₁ E₂ m n : ℕ}
    (fExternal : Fin (2 * E₁) → Fin (2 * E₂)) (fInteraction : Fin m → Fin n)
    (v : ↥(Finset.univ : Finset (Fin m))) (l : Fin 4) :
    orderedExternalInsertionLegMap fExternal fInteraction (Sum.inr (v, l)) =
      Sum.inr (⟨fInteraction v.1, Finset.mem_univ _⟩, l) := rfl

/-- Injective slot reindexings induce an injective canonical-leg reindexing. -/
theorem orderedExternalInsertionLegMap_injective {E₁ E₂ m n : ℕ}
    {fExternal : Fin (2 * E₁) → Fin (2 * E₂)} {fInteraction : Fin m → Fin n}
    (hExternal : Function.Injective fExternal)
    (hInteraction : Function.Injective fInteraction) :
    Function.Injective (orderedExternalInsertionLegMap fExternal fInteraction) := by
  unfold orderedExternalInsertionLegMap
  apply Function.Injective.sumMap hExternal
  apply Function.Injective.prodMap
  · intro v w h
    exact Subtype.ext (hInteraction (congrArg Subtype.val h))
  · exact Function.injective_id

/-- Atomic legs contributed by one mixed event. -/
private def externalInsertionTimedEventAtomicLegs {E n : ℕ} :
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
  cases event <;> simp [externalInsertionTimedEventAtomicLegs]

/-- Atomic leg identities in mixed-time event order. -/
private noncomputable def externalInsertionMixedTimeOrderedAtomicLegs {E n : ℕ}
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
  cases a with
  | inl e =>
      cases b with
      | inl e' => simpa [externalInsertionTimedEventAtomicLegs] using h.symm
      | inr v => simp [externalInsertionTimedEventAtomicLegs]
  | inr v =>
      cases b with
      | inl e => simp [externalInsertionTimedEventAtomicLegs]
      | inr v' =>
          have hv : v ≠ v' := by
            intro hv
            apply h
            cases hv
            rfl
          simpa [externalInsertionTimedEventAtomicLegs] using hv.symm

private theorem externalInsertionMixedTimeOrderedAtomicLegs_nodup {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    (externalInsertionMixedTimeOrderedAtomicLegs externalTime σ).Nodup := by
  rw [externalInsertionMixedTimeOrderedAtomicLegs, List.nodup_flatMap]
  refine ⟨
    fun event _ => externalInsertionTimedEventAtomicLegs_nodup event,
    ?_⟩
  exact
    (orderedExternalInsertionTimedEvents_nodup externalTime σ).pairwise_of_forall_ne
      (fun _ _ _ _ h => externalInsertionTimedEventAtomicLegs_disjoint h)

private theorem externalInsertionMixedTimeOrderedAtomicLegs_all_mem {E n : ℕ}
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

private theorem externalInsertionMixedTimeOrderedAtomicLegs_length {E n : ℕ}
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

/-- The mixed position occupied by a canonical external-insertion leg identity. -/
noncomputable def externalInsertionMixedTimeOrderedAtomicLegPosition {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (leg : OrderedExternalInsertionLeg E n) : Fin (2 * (2 * n + E)) :=
  (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ).symm leg

@[simp]
theorem externalInsertionMixedTimeOrderedAtomicLegPosition_equiv {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (p : Fin (2 * (2 * n + E))) :
    externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
        (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ p) = p :=
  (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ).symm_apply_apply p

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

/-- Permutation from the fixed flattened diagram-leg order to mixed-time atomic positions. -/
noncomputable def externalInsertionStandardToMixedAtomicPositionEquiv {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    Equiv.Perm (Fin (2 * (2 * n + E))) :=
  (finCongr (by simp)).trans
    ((externalInsertionLegEquiv E (Finset.univ : Finset (Fin n))).trans
      (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ).symm)

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

end Common
end SecondQuantization
