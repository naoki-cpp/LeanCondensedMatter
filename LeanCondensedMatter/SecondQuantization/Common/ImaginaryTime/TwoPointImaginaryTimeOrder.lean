import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.ExternalInsertionImaginaryTimeOrder
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Tactic.FinCases

set_option linter.style.header false

/-!
# Imaginary-time event order for two-point insertions

A two-point insertion contributes two distinguished external events together with `n` interaction
events. This module orders those events by decreasing imaginary time, using a deterministic stable
rank at equal times: external event `0`, external event `1`, then interaction slots in their supplied
order.

The construction only defines the event order and its deterministic equal-time convention.
It does not implement the fermionic imaginary-time ordering operator: signs are downstream.

The construction is purely order-theoretic. It does not know which operators the events represent,
which statistics they obey, or which exchange factor an operator realization assigns when the two
external events are exchanged. Statistics-specific layers map the ordered events to operators and
supply any exchange prefactor separately.
-/

namespace SecondQuantization
namespace Common

/-- The event type for a two-point insertion with `n` interaction vertices: two distinguished
external events followed by the interaction slots. -/
abbrev TwoPointTimedEvent (n : ℕ) : Type := Fin 2 ⊕ Fin n

/-- The two fixed external times in their canonical external-event order. -/
def twoPointExternalTimes (τ τ' : ℝ) : Fin 2 → ℝ :=
  fun e => if e = 0 then τ else τ'

@[simp]
theorem twoPointExternalTimes_zero (τ τ' : ℝ) : twoPointExternalTimes τ τ' 0 = τ := by
  simp [twoPointExternalTimes]

@[simp]
theorem twoPointExternalTimes_one (τ τ' : ℝ) : twoPointExternalTimes τ τ' 1 = τ' := by
  simp [twoPointExternalTimes]

/-- The imaginary time attached to an external or interaction event. -/
def twoPointTimedEventTime {n : ℕ} (τ τ' : ℝ) (σ : Fin n → ℝ) :
    TwoPointTimedEvent n → ℝ
  | .inl e => twoPointExternalTimes τ τ' e
  | .inr v => σ v

/-- Stable equal-time rank: external events have ranks `0,1` and interaction slot `v` has rank
`2 + v`. -/
def twoPointTimedEventRank {n : ℕ} (event : TwoPointTimedEvent n) : ℕ :=
  (finSumFinEquiv event : Fin (2 + n)).val

/-- Stable non-strict event precedence: later imaginary time comes first, with the stable rank
breaking equal-time ties. -/
def twoPointTimedEventBeforeOrEqual {n : ℕ} (τ τ' : ℝ) (σ : Fin n → ℝ)
    (a b : TwoPointTimedEvent n) : Prop :=
  stableTimedEventBeforeOrEqual (twoPointTimedEventTime τ τ' σ) twoPointTimedEventRank a b

/-- Strict stable event precedence, obtained by excluding equality from
`twoPointTimedEventBeforeOrEqual`. -/
def twoPointTimedEventBefore {n : ℕ} (τ τ' : ℝ) (σ : Fin n → ℝ)
    (a b : TwoPointTimedEvent n) : Prop :=
  twoPointTimedEventBeforeOrEqual τ τ' σ a b ∧ a ≠ b

/-- Interaction events in their canonical supplied slot order. -/
def twoPointInteractionEventList (n : ℕ) : List (TwoPointTimedEvent n) :=
  List.ofFn fun v : Fin n => Sum.inr v

/-- All external and interaction events sorted by decreasing time with the stable equal-time rank. -/
noncomputable def orderedTwoPointTimedEvents {n : ℕ} (τ τ' : ℝ) (σ : Fin n → ℝ) :
    List (TwoPointTimedEvent n) := by
  classical
  exact List.insertionSort (twoPointTimedEventBeforeOrEqual τ τ' σ)
    ([Sum.inl 0, Sum.inl 1] ++ twoPointInteractionEventList n)

@[simp]
private theorem orderedTwoPointTimedEvents_length {n : ℕ} (τ τ' : ℝ) (σ : Fin n → ℝ) :
    (orderedTwoPointTimedEvents τ τ' σ).length = n + 2 := by
  classical
  rw [orderedTwoPointTimedEvents, List.length_insertionSort]
  simp [twoPointInteractionEventList]

/-- Time ordering permutes, but neither duplicates nor removes, the canonical mixed events. -/
theorem orderedTwoPointTimedEvents_perm {n : ℕ} (τ τ' : ℝ) (σ : Fin n → ℝ) :
    List.Perm (orderedTwoPointTimedEvents τ τ' σ)
      ([Sum.inl 0, Sum.inl 1] ++ twoPointInteractionEventList n) := by
  classical
  exact List.perm_insertionSort _ _

/-- The fully ordered mixed-event list is pairwise sorted by stable time precedence. -/
theorem orderedTwoPointTimedEvents_pairwise {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    (orderedTwoPointTimedEvents τ τ' σ).Pairwise
      (twoPointTimedEventBeforeOrEqual τ τ' σ) := by
  classical
  change (List.insertionSort
      (stableTimedEventBeforeOrEqual (twoPointTimedEventTime τ τ' σ) twoPointTimedEventRank)
      ([Sum.inl 0, Sum.inl 1] ++ twoPointInteractionEventList n)).Pairwise
        (stableTimedEventBeforeOrEqual (twoPointTimedEventTime τ τ' σ) twoPointTimedEventRank)
  exact List.pairwise_insertionSort _ _

/-- The fully ordered mixed-event list contains no duplicate events. -/
theorem orderedTwoPointTimedEvents_nodup {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    (orderedTwoPointTimedEvents τ τ' σ).Nodup :=
  (orderedTwoPointTimedEvents_perm τ τ' σ).nodup_iff.mpr (by
    rw [twoPointInteractionEventList]
    change ((Sum.inl (0 : Fin 2) : TwoPointTimedEvent n) ::
      (Sum.inl (1 : Fin 2) : TwoPointTimedEvent n) ::
        List.ofFn (fun v : Fin n => (Sum.inr v : TwoPointTimedEvent n))).Nodup
    refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, ?_⟩⟩
    · simp
    · simp
    · exact List.nodup_ofFn_ofInjective Sum.inr_injective)

/-- Every external or interaction event occurs in the fully ordered event list. -/
theorem orderedTwoPointTimedEvents_all_mem {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    ∀ event : TwoPointTimedEvent n,
      event ∈ orderedTwoPointTimedEvents τ τ' σ := by
  intro event
  apply (orderedTwoPointTimedEvents_perm τ τ' σ).symm.subset
  cases event with
  | inl e => fin_cases e <;> simp [twoPointInteractionEventList]
  | inr v => simp [twoPointInteractionEventList]

/-- The two-point and arbitrary-external stable event orders coincide for two
external slots, including all equal-time ties. -/
theorem orderedTwoPointTimedEvents_eq_externalInsertion {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    orderedTwoPointTimedEvents τ τ' σ =
      orderedExternalInsertionTimedEvents (E := 1) (twoPointExternalTimes τ τ') σ := by
  classical
  let source := orderedTwoPointTimedEvents τ τ' σ
  let target := orderedExternalInsertionTimedEvents (E := 1) (twoPointExternalTimes τ τ') σ
  let rel := twoPointTimedEventBeforeOrEqual τ τ' σ
  have hSubperm : List.Subperm source target :=
    (orderedTwoPointTimedEvents_nodup τ τ' σ).subperm
      (fun event _ => orderedExternalInsertionTimedEvents_all_mem
        (E := 1) (twoPointExternalTimes τ τ') σ event)
  letI : Std.Antisymm rel :=
    ⟨fun _ _ hab hba =>
      stableTimedEventBeforeOrEqual_antisymm
        (twoPointTimedEventTime τ τ' σ) twoPointTimedEventRank
        (by
          intro a b h
          apply (finSumFinEquiv : TwoPointTimedEvent n ≃ Fin (2 + n)).injective
          exact Fin.ext h)
        hab hba⟩
  have htime : externalInsertionTimedEventTime (E := 1) (twoPointExternalTimes τ τ') σ =
      twoPointTimedEventTime τ τ' σ := by
    funext e
    cases e <;> rfl
  have ht : target.Pairwise rel := by
    change (orderedExternalInsertionTimedEvents (E := 1) (twoPointExternalTimes τ τ') σ).Pairwise
      (stableTimedEventBeforeOrEqual (twoPointTimedEventTime τ τ' σ)
        (fun e : TwoPointTimedEvent n => (finSumFinEquiv e : Fin (2 + n)).val))
    rw [← htime]
    exact orderedExternalInsertionTimedEvents_pairwise
      (E := 1) (twoPointExternalTimes τ τ') σ
  have hs : source.Pairwise rel := orderedTwoPointTimedEvents_pairwise τ τ' σ
  have hsub := List.sublist_of_subperm_of_pairwise (r := rel) hSubperm hs ht
  have hRev : List.Subperm target source :=
    (orderedExternalInsertionTimedEvents_nodup
      (E := 1) (twoPointExternalTimes τ τ') σ).subperm
      (fun event _ => orderedTwoPointTimedEvents_all_mem τ τ' σ event)
  exact hsub.eq_of_length (le_antisymm hsub.length_le hRev.length_le)

/-- Exact enumeration of all mixed events by their time-ordered positions. -/
noncomputable def orderedTwoPointTimedEventEquiv {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    Fin (n + 2) ≃ TwoPointTimedEvent n :=
  (finCongr (orderedTwoPointTimedEvents_length τ τ' σ).symm).trans
    (List.Nodup.getEquivOfForallMemList
      (orderedTwoPointTimedEvents τ τ' σ)
      (orderedTwoPointTimedEvents_nodup τ τ' σ)
      (orderedTwoPointTimedEvents_all_mem τ τ' σ))

/-- Position occupied by one event in the fully ordered mixed-event list. -/
noncomputable def orderedTwoPointTimedEventPosition {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) (event : TwoPointTimedEvent n) : Fin (n + 2) :=
  (orderedTwoPointTimedEventEquiv τ τ' σ).symm event

/-- Event-position comparison is exactly strict stable time precedence. -/
theorem orderedTwoPointTimedEventPosition_lt_iff {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) (a b : TwoPointTimedEvent n) :
    orderedTwoPointTimedEventPosition τ τ' σ a <
        orderedTwoPointTimedEventPosition τ τ' σ b ↔
      twoPointTimedEventBefore τ τ' σ a b := by
  classical
  by_cases hab : a = b
  · subst b
    simp [twoPointTimedEventBefore]
  · let rel := twoPointTimedEventBeforeOrEqual τ τ' σ
    letI : Std.Antisymm rel :=
      ⟨fun _ _ h₁ h₂ => stableTimedEventBeforeOrEqual_antisymm
        (twoPointTimedEventTime τ τ' σ) twoPointTimedEventRank
        (by
          intro x y h
          exact (finSumFinEquiv : TwoPointTimedEvent n ≃ Fin (2 + n)).injective (Fin.ext h))
        h₁ h₂⟩
    have hs : (orderedTwoPointTimedEvents τ τ' σ).Pairwise rel :=
      orderedTwoPointTimedEvents_pairwise τ τ' σ
    have h := hs.idxOf_lt_iff_of_ne
      (orderedTwoPointTimedEvents_all_mem τ τ' σ a)
      (orderedTwoPointTimedEvents_all_mem τ τ' σ b) hab
    simpa [rel, hab, twoPointTimedEventBefore, orderedTwoPointTimedEventPosition,
      orderedTwoPointTimedEventEquiv, List.Nodup.getEquivOfForallMemList] using h

/-- At two external insertions, the full atomic permutation reverses sign
exactly when the two external fields are exchanged. Interaction times,
including all equal-time ties, impose no further sign. -/
theorem externalInsertionStandardToMixedAtomicPositionEquiv_sign_twoPoint
    {n : ℕ} (τ τ' : ℝ) (σ : Fin n → ℝ) :
    Equiv.Perm.sign
        (externalInsertionStandardToMixedAtomicPositionEquiv
          (E := 1) (twoPointExternalTimes τ τ') σ) =
      (if τ < τ' then (-1 : ℤˣ) else 1) := by
  classical
  rw [externalInsertionStandardToMixedAtomicPositionEquiv_sign]
  change (-1 : ℤˣ) ^ (∑ a : Fin 2, ∑ b : Fin 2,
    if a.val < b.val ∧ twoPointExternalTimes τ τ' a < twoPointExternalTimes τ τ' b
    then 1 else 0) = _
  simp only [Fin.sum_univ_two]
  by_cases h : τ < τ' <;> simp [h]


/-! ## Monotone interaction-slot transport -/

variable {m n : ℕ} {f : Fin m → Fin n}

/-- Transport a mixed event along a reindexing of the interaction slots, fixing the two external
events. -/
def twoPointTimedEventMap (f : Fin m → Fin n) : TwoPointTimedEvent m → TwoPointTimedEvent n :=
  Sum.map id f

@[simp]
theorem twoPointTimedEventMap_inl (f : Fin m → Fin n) (e : Fin 2) :
    twoPointTimedEventMap f (Sum.inl e) = Sum.inl e := rfl

@[simp]
theorem twoPointTimedEventMap_inr (f : Fin m → Fin n) (v : Fin m) :
    twoPointTimedEventMap f (Sum.inr v) = Sum.inr (f v) := rfl

/-- Injective slot reindexings induce injective event reindexings. -/
theorem twoPointTimedEventMap_injective (hf : Function.Injective f) :
    Function.Injective (twoPointTimedEventMap f) := by
  simpa [twoPointTimedEventMap] using
    (Sum.map_injective.mpr ⟨Function.injective_id, hf⟩)

private theorem twoPointTimedEventTime_map (f : Fin m → Fin n) (τ τ' : ℝ)
    (σ : Fin n → ℝ) (a : TwoPointTimedEvent m) :
    twoPointTimedEventTime τ τ' σ (twoPointTimedEventMap f a) =
      twoPointTimedEventTime τ τ' (σ ∘ f) a := by
  cases a <;> rfl

private theorem twoPointTimedEventBeforeOrEqual_map_iff
    (hf : StrictMono f) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (a b : TwoPointTimedEvent m) :
    twoPointTimedEventBeforeOrEqual τ τ' σ
        (twoPointTimedEventMap f a) (twoPointTimedEventMap f b) ↔
      twoPointTimedEventBeforeOrEqual τ τ' (σ ∘ f) a b := by
  simp only [twoPointTimedEventBeforeOrEqual, stableTimedEventBeforeOrEqual_iff,
    twoPointTimedEventTime_map]
  have hrank :
      twoPointTimedEventRank (twoPointTimedEventMap f a) ≤
        twoPointTimedEventRank (twoPointTimedEventMap f b) ↔
          twoPointTimedEventRank a ≤ twoPointTimedEventRank b := by
    simpa [twoPointTimedEventMap, twoPointTimedEventRank] using
      (finSumFinEquiv_map_val_le_iff
        (f := id) (g := f)
        (show StrictMono (id : Fin 2 → Fin 2) from fun _ _ h => h)
        hf a b)
  rw [hrank]

private theorem twoPointTimedEventBefore_map_iff
    (hf : StrictMono f) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (a b : TwoPointTimedEvent m) :
    twoPointTimedEventBefore τ τ' σ (twoPointTimedEventMap f a) (twoPointTimedEventMap f b) ↔
      twoPointTimedEventBefore τ τ' (σ ∘ f) a b := by
  simp only [twoPointTimedEventBefore]
  rw [twoPointTimedEventBeforeOrEqual_map_iff hf]
  constructor
  · rintro ⟨h, hne⟩
    exact ⟨h, fun hab => hne (congrArg (twoPointTimedEventMap f) hab)⟩
  · rintro ⟨h, hne⟩
    exact ⟨h, fun hab => hne (twoPointTimedEventMap_injective hf.injective hab)⟩

/-- A strictly monotone slot reindexing preserves the relative positions of the transported mixed
events. -/
theorem orderedTwoPointTimedEventPosition_map_lt_iff (hf : StrictMono f) (τ τ' : ℝ)
    (σ : Fin n → ℝ) (a b : TwoPointTimedEvent m) :
    orderedTwoPointTimedEventPosition τ τ' σ (twoPointTimedEventMap f a) <
        orderedTwoPointTimedEventPosition τ τ' σ (twoPointTimedEventMap f b) ↔
      orderedTwoPointTimedEventPosition τ τ' (σ ∘ f) a <
        orderedTwoPointTimedEventPosition τ τ' (σ ∘ f) b := by
  rw [orderedTwoPointTimedEventPosition_lt_iff, orderedTwoPointTimedEventPosition_lt_iff,
    twoPointTimedEventBefore_map_iff hf]

end Common
end SecondQuantization
