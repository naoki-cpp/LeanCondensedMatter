import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized.PeelFirst
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.QuarticInteraction
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.ExternalField
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.InteractionPicture
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Pairwise

set_option linter.style.header false

/-!
# Mixed imaginary-time ordering for a two-point insertion

This module combines the two odd external fields of a fermionic two-point function with quartic
interaction vertices. All external and interaction events are ordered together by decreasing
imaginary time. Equal-time events use a deterministic stable rank: external event `0`, then external
event `1`, then interaction vertices in their supplied order.

On the ordered simplex, the interaction vertices already occur in decreasing-time slot order, so
this full event sort agrees with the Dyson ordering used by the perturbative expansion. Away from the
ordered simplex it provides a canonical extension whose relative order on any subset of events
depends only on those events' own times and stable ranks.

Only exchanging the two external fields contributes the explicit fermionic prefactor. Moving an
external field past a quartic interaction vertex contributes no sign because the quartic vertex is
even. The standalone `twoPointTimeOrderedProduct` retains the symmetric `theta(0) = 1/2` convention
for equal external times.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode]

/-- The event type for a two-point insertion with `n` quartic interaction vertices. -/
abbrev TwoPointTimedEvent (n : ℕ) : Type := Fin 2 ⊕ Fin n

/-- The two fixed external times, in the canonical annihilation/creation order. -/
def twoPointExternalTimes (τ τ' : ℝ) : Fin 2 → ℝ :=
  fun e => if e = 0 then τ else τ'

@[simp]
theorem twoPointExternalTimes_zero (τ τ' : ℝ) : twoPointExternalTimes τ τ' 0 = τ := by
  simp [twoPointExternalTimes]

@[simp]
theorem twoPointExternalTimes_one (τ τ' : ℝ) : twoPointExternalTimes τ τ' 1 = τ' := by
  simp [twoPointExternalTimes]

/-- The time attached to an external or interaction event. -/
def twoPointTimedEventTime {n : ℕ} (τ τ' : ℝ) (σ : Fin n → ℝ) :
    TwoPointTimedEvent n → ℝ
  | .inl e => twoPointExternalTimes τ τ' e
  | .inr v => σ v

/-- Stable tie-breaking rank: the two external events precede interaction vertices, and interaction
vertices retain their supplied order. -/
def twoPointTimedEventRank {n : ℕ} : TwoPointTimedEvent n → ℕ
  | .inl e => e
  | .inr v => 2 + v

/-- `a` should be placed before `b`: later imaginary time first, with the stable rank used at equal
times. -/
def twoPointTimedEventBeforeOrEqual {n : ℕ} (τ τ' : ℝ) (σ : Fin n → ℝ)
    (a b : TwoPointTimedEvent n) : Prop :=
  twoPointTimedEventTime τ τ' σ b < twoPointTimedEventTime τ τ' σ a ∨
    (twoPointTimedEventTime τ τ' σ a = twoPointTimedEventTime τ τ' σ b ∧
      twoPointTimedEventRank a ≤ twoPointTimedEventRank b)

/-- Strict mixed-event precedence. The non-equality removes the reflexive equal-time case from the
stable preorder. -/
def twoPointTimedEventBefore {n : ℕ} (τ τ' : ℝ) (σ : Fin n → ℝ)
    (a b : TwoPointTimedEvent n) : Prop :=
  twoPointTimedEventBeforeOrEqual τ τ' σ a b ∧ a ≠ b

private theorem twoPointTimedEventRank_injective {n : ℕ} :
    Function.Injective (twoPointTimedEventRank : TwoPointTimedEvent n → ℕ) := by
  intro a b h
  cases a with
  | inl a =>
      cases b with
      | inl b =>
          apply congrArg Sum.inl
          apply Fin.ext
          simpa [twoPointTimedEventRank] using h
      | inr b =>
          simp [twoPointTimedEventRank] at h
          omega
  | inr a =>
      cases b with
      | inl b =>
          simp [twoPointTimedEventRank] at h
          omega
      | inr b =>
          apply congrArg Sum.inr
          apply Fin.ext
          simpa [twoPointTimedEventRank] using h

private theorem twoPointTimedEventBeforeOrEqual_total {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) (a b : TwoPointTimedEvent n) :
    twoPointTimedEventBeforeOrEqual τ τ' σ a b ∨
      twoPointTimedEventBeforeOrEqual τ τ' σ b a := by
  rcases lt_trichotomy
      (twoPointTimedEventTime τ τ' σ a)
      (twoPointTimedEventTime τ τ' σ b) with hab | hab | hab
  · right
    exact Or.inl hab
  · rcases le_total (twoPointTimedEventRank a) (twoPointTimedEventRank b) with hr | hr
    · left
      exact Or.inr ⟨hab, hr⟩
    · right
      exact Or.inr ⟨hab.symm, hr⟩
  · left
    exact Or.inl hab

private theorem twoPointTimedEventBeforeOrEqual_trans {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) {a b c : TwoPointTimedEvent n}
    (hab : twoPointTimedEventBeforeOrEqual τ τ' σ a b)
    (hbc : twoPointTimedEventBeforeOrEqual τ τ' σ b c) :
    twoPointTimedEventBeforeOrEqual τ τ' σ a c := by
  rcases hab with hab | ⟨habTime, habRank⟩
  · rcases hbc with hbc | ⟨hbcTime, _⟩
    · exact Or.inl (lt_trans hbc hab)
    · exact Or.inl (hbcTime ▸ hab)
  · rcases hbc with hbc | ⟨hbcTime, hbcRank⟩
    · exact Or.inl (habTime ▸ hbc)
    · exact Or.inr ⟨habTime.trans hbcTime, habRank.trans hbcRank⟩

private theorem twoPointTimedEventBeforeOrEqual_antisymm {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) {a b : TwoPointTimedEvent n}
    (hab : twoPointTimedEventBeforeOrEqual τ τ' σ a b)
    (hba : twoPointTimedEventBeforeOrEqual τ τ' σ b a) :
    a = b := by
  rcases hab with hab | ⟨habTime, habRank⟩
  · rcases hba with hba | ⟨hbaTime, _⟩
    · exact (lt_asymm hab hba).elim
    · rw [hbaTime] at hab
      exact (lt_irrefl _ hab).elim
  · rcases hba with hba | ⟨_, hbaRank⟩
    · rw [habTime] at hba
      exact (lt_irrefl _ hba).elim
    · exact twoPointTimedEventRank_injective (habRank.antisymm hbaRank)

/-- The stable comparison of two fixed events is unchanged when their two event times are unchanged.
-/
theorem twoPointTimedEventBeforeOrEqual_congr {n : ℕ}
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (a b : TwoPointTimedEvent n)
    (ha : twoPointTimedEventTime τ τ' σ a = twoPointTimedEventTime τ τ' υ a)
    (hb : twoPointTimedEventTime τ τ' σ b = twoPointTimedEventTime τ τ' υ b) :
    twoPointTimedEventBeforeOrEqual τ τ' σ a b ↔
      twoPointTimedEventBeforeOrEqual τ τ' υ a b := by
  simp only [twoPointTimedEventBeforeOrEqual]
  rw [ha, hb]

private noncomputable def insertTwoPointTimedEvent {n : ℕ} (τ τ' : ℝ) (σ : Fin n → ℝ)
    (a : TwoPointTimedEvent n) : List (TwoPointTimedEvent n) → List (TwoPointTimedEvent n)
  | [] => [a]
  | b :: l =>
      @ite (List (TwoPointTimedEvent n)) (twoPointTimedEventBeforeOrEqual τ τ' σ a b)
        (Classical.propDecidable _)
        (a :: b :: l) (b :: insertTwoPointTimedEvent τ τ' σ a l)

private theorem insertTwoPointTimedEvent_length {n : ℕ} (τ τ' : ℝ) (σ : Fin n → ℝ)
    (a : TwoPointTimedEvent n) (l : List (TwoPointTimedEvent n)) :
    (insertTwoPointTimedEvent τ τ' σ a l).length = l.length + 1 := by
  induction l with
  | nil => rfl
  | cons b l ih =>
      rw [insertTwoPointTimedEvent]
      split <;> simp [ih]

private theorem insertTwoPointTimedEvent_perm {n : ℕ} (τ τ' : ℝ) (σ : Fin n → ℝ)
    (a : TwoPointTimedEvent n) (l : List (TwoPointTimedEvent n)) :
    List.Perm (insertTwoPointTimedEvent τ τ' σ a l) (a :: l) := by
  induction l with
  | nil => simp [insertTwoPointTimedEvent]
  | cons b l ih =>
      rw [insertTwoPointTimedEvent]
      split
      · exact List.Perm.refl _
      · exact (List.Perm.cons b ih).trans (List.Perm.swap b a l).symm

private theorem insertTwoPointTimedEvent_pairwise {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) (a : TwoPointTimedEvent n)
    (l : List (TwoPointTimedEvent n))
    (hl : l.Pairwise (twoPointTimedEventBeforeOrEqual τ τ' σ)) :
    (insertTwoPointTimedEvent τ τ' σ a l).Pairwise
      (twoPointTimedEventBeforeOrEqual τ τ' σ) := by
  induction l with
  | nil => simp [insertTwoPointTimedEvent]
  | cons b l ih =>
      cases hl with
      | cons hbl hl =>
          rw [insertTwoPointTimedEvent]
          split
          next hab =>
            refine List.Pairwise.cons ?_ (List.Pairwise.cons hbl hl)
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact hab
            · exact twoPointTimedEventBeforeOrEqual_trans τ τ' σ hab (hbl x hx)
          next hab =>
            have hba : twoPointTimedEventBeforeOrEqual τ τ' σ b a :=
              (twoPointTimedEventBeforeOrEqual_total τ τ' σ a b).resolve_left hab
            refine List.Pairwise.cons ?_ (ih hl)
            intro x hx
            have hx' : x ∈ a :: l :=
              (insertTwoPointTimedEvent_perm τ τ' σ a l).mem_iff.mp hx
            rcases List.mem_cons.mp hx' with rfl | hx'
            · exact hba
            · exact hbl x hx'

/-- Insertion-sort all mixed events by decreasing imaginary time and stable rank. -/
private noncomputable def sortTwoPointTimedEvents {n : ℕ} (τ τ' : ℝ) (σ : Fin n → ℝ) :
    List (TwoPointTimedEvent n) → List (TwoPointTimedEvent n)
  | [] => []
  | a :: l => insertTwoPointTimedEvent τ τ' σ a
      (sortTwoPointTimedEvents τ τ' σ l)

private theorem sortTwoPointTimedEvents_length {n : ℕ} (τ τ' : ℝ) (σ : Fin n → ℝ)
    (l : List (TwoPointTimedEvent n)) :
    (sortTwoPointTimedEvents τ τ' σ l).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [sortTwoPointTimedEvents, insertTwoPointTimedEvent_length, ih]
      simp

private theorem sortTwoPointTimedEvents_perm {n : ℕ} (τ τ' : ℝ) (σ : Fin n → ℝ)
    (l : List (TwoPointTimedEvent n)) :
    List.Perm (sortTwoPointTimedEvents τ τ' σ l) l := by
  induction l with
  | nil => exact List.Perm.refl []
  | cons a l ih =>
      exact (insertTwoPointTimedEvent_perm τ τ' σ a
        (sortTwoPointTimedEvents τ τ' σ l)).trans (List.Perm.cons a ih)

private theorem sortTwoPointTimedEvents_pairwise {n : ℕ} (τ τ' : ℝ) (σ : Fin n → ℝ)
    (l : List (TwoPointTimedEvent n)) :
    (sortTwoPointTimedEvents τ τ' σ l).Pairwise
      (twoPointTimedEventBeforeOrEqual τ τ' σ) := by
  induction l with
  | nil => simp [sortTwoPointTimedEvents]
  | cons a l ih =>
      exact insertTwoPointTimedEvent_pairwise τ τ' σ a
        (sortTwoPointTimedEvents τ τ' σ l) ih

/-- The interaction events in their canonical supplied slot order. -/
def twoPointInteractionEventList (n : ℕ) : List (TwoPointTimedEvent n) :=
  List.ofFn fun v : Fin n => Sum.inr v

private theorem canonicalTwoPointTimedEvents_nodup (n : ℕ) :
    ([Sum.inl 0, Sum.inl 1] ++ twoPointInteractionEventList n).Nodup := by
  rw [twoPointInteractionEventList]
  change ((Sum.inl (0 : Fin 2) : TwoPointTimedEvent n) ::
    (Sum.inl (1 : Fin 2) : TwoPointTimedEvent n) ::
      List.ofFn (fun v : Fin n => (Sum.inr v : TwoPointTimedEvent n))).Nodup
  refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, ?_⟩⟩
  · simp
  · simp
  · exact List.nodup_ofFn_ofInjective Sum.inr_injective

private theorem canonicalTwoPointTimedEvents_all_mem (n : ℕ) :
    ∀ event : TwoPointTimedEvent n,
      event ∈ [Sum.inl 0, Sum.inl 1] ++ twoPointInteractionEventList n := by
  intro event
  cases event with
  | inl e => fin_cases e <;> simp [twoPointInteractionEventList]
  | inr v => simp [twoPointInteractionEventList]

/-- Order the two external events and every interaction event together by decreasing time. -/
noncomputable def orderedTwoPointTimedEvents {n : ℕ} (τ τ' : ℝ) (σ : Fin n → ℝ) :
    List (TwoPointTimedEvent n) :=
  sortTwoPointTimedEvents τ τ' σ
    ([Sum.inl 0, Sum.inl 1] ++ twoPointInteractionEventList n)

@[simp]
theorem orderedTwoPointTimedEvents_length {n : ℕ} (τ τ' : ℝ) (σ : Fin n → ℝ) :
    (orderedTwoPointTimedEvents τ τ' σ).length = n + 2 := by
  rw [orderedTwoPointTimedEvents, sortTwoPointTimedEvents_length]
  simp [twoPointInteractionEventList]

/-- Time ordering permutes, but neither duplicates nor removes, the two external events and the
interaction events. -/
theorem orderedTwoPointTimedEvents_perm {n : ℕ} (τ τ' : ℝ) (σ : Fin n → ℝ) :
    List.Perm (orderedTwoPointTimedEvents τ τ' σ)
      ([Sum.inl 0, Sum.inl 1] ++ twoPointInteractionEventList n) := by
  exact sortTwoPointTimedEvents_perm τ τ' σ _

/-- The fully ordered mixed-event list is sorted by the stable time comparison. -/
theorem orderedTwoPointTimedEvents_pairwise {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    (orderedTwoPointTimedEvents τ τ' σ).Pairwise
      (twoPointTimedEventBeforeOrEqual τ τ' σ) := by
  exact sortTwoPointTimedEvents_pairwise τ τ' σ _

/-- The fully ordered mixed-event list has no duplicate events. -/
theorem orderedTwoPointTimedEvents_nodup {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    (orderedTwoPointTimedEvents τ τ' σ).Nodup :=
  (orderedTwoPointTimedEvents_perm τ τ' σ).nodup_iff.mpr
    (canonicalTwoPointTimedEvents_nodup n)

/-- Every external or interaction event occurs in the fully ordered event list. -/
theorem orderedTwoPointTimedEvents_all_mem {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    ∀ event : TwoPointTimedEvent n,
      event ∈ orderedTwoPointTimedEvents τ τ' σ := by
  intro event
  exact (orderedTwoPointTimedEvents_perm τ τ' σ).symm.subset
    (canonicalTwoPointTimedEvents_all_mem n event)

/-- Exact enumeration of all mixed events by their time-ordered positions. -/
noncomputable def orderedTwoPointTimedEventEquiv {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    Fin (n + 2) ≃ TwoPointTimedEvent n :=
  (finCongr (orderedTwoPointTimedEvents_length τ τ' σ).symm).trans
    (List.Nodup.getEquivOfForallMemList
      (orderedTwoPointTimedEvents τ τ' σ)
      (orderedTwoPointTimedEvents_nodup τ τ' σ)
      (orderedTwoPointTimedEvents_all_mem τ τ' σ))

/-- Position occupied by one external or interaction event in the fully ordered event list. -/
noncomputable def orderedTwoPointTimedEventPosition {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) (event : TwoPointTimedEvent n) : Fin (n + 2) :=
  (orderedTwoPointTimedEventEquiv τ τ' σ).symm event

@[simp]
theorem orderedTwoPointTimedEventEquiv_position {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) (event : TwoPointTimedEvent n) :
    orderedTwoPointTimedEventEquiv τ τ' σ
        (orderedTwoPointTimedEventPosition τ τ' σ event) = event :=
  (orderedTwoPointTimedEventEquiv τ τ' σ).apply_symm_apply event

private theorem twoPointTimedEventBeforeOrEqual_of_position_lt {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) {a b : TwoPointTimedEvent n}
    (h : orderedTwoPointTimedEventPosition τ τ' σ a <
      orderedTwoPointTimedEventPosition τ τ' σ b) :
    twoPointTimedEventBeforeOrEqual τ τ' σ a b := by
  let l := orderedTwoPointTimedEvents τ τ' σ
  let pa : Fin l.length :=
    Fin.cast (orderedTwoPointTimedEvents_length τ τ' σ).symm
      (orderedTwoPointTimedEventPosition τ τ' σ a)
  let pb : Fin l.length :=
    Fin.cast (orderedTwoPointTimedEvents_length τ τ' σ).symm
      (orderedTwoPointTimedEventPosition τ τ' σ b)
  have hp : pa < pb := by
    simpa [pa, pb] using h
  have hrel := (orderedTwoPointTimedEvents_pairwise τ τ' σ).rel_get_of_lt hp
  have ha : l.get pa = a := by
    change (List.Nodup.getEquivOfForallMemList l
      (orderedTwoPointTimedEvents_nodup τ τ' σ)
      (orderedTwoPointTimedEvents_all_mem τ τ' σ)) pa = a
    simpa [pa, orderedTwoPointTimedEventPosition,
      orderedTwoPointTimedEventEquiv] using
      (orderedTwoPointTimedEventEquiv τ τ' σ).apply_symm_apply a
  have hb : l.get pb = b := by
    change (List.Nodup.getEquivOfForallMemList l
      (orderedTwoPointTimedEvents_nodup τ τ' σ)
      (orderedTwoPointTimedEvents_all_mem τ τ' σ)) pb = b
    simpa [pb, orderedTwoPointTimedEventPosition,
      orderedTwoPointTimedEventEquiv] using
      (orderedTwoPointTimedEventEquiv τ τ' σ).apply_symm_apply b
  simpa [l, ha, hb] using hrel

/-- Event-position comparison is exactly strict stable time precedence. -/
theorem orderedTwoPointTimedEventPosition_lt_iff {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) (a b : TwoPointTimedEvent n) :
    orderedTwoPointTimedEventPosition τ τ' σ a <
        orderedTwoPointTimedEventPosition τ τ' σ b ↔
      twoPointTimedEventBefore τ τ' σ a b := by
  constructor
  · intro h
    refine ⟨twoPointTimedEventBeforeOrEqual_of_position_lt τ τ' σ h, ?_⟩
    intro hab
    subst b
    exact (lt_irrefl _ h)
  · rintro ⟨hab, hne⟩
    rcases lt_trichotomy
        (orderedTwoPointTimedEventPosition τ τ' σ a)
        (orderedTwoPointTimedEventPosition τ τ' σ b) with h | h | h
    · exact h
    · exact (hne ((orderedTwoPointTimedEventEquiv τ τ' σ).symm.injective h)).elim
    · have hba := twoPointTimedEventBeforeOrEqual_of_position_lt τ τ' σ h
      exact (hne (twoPointTimedEventBeforeOrEqual_antisymm τ τ' σ hab hba)).elim

/-- The relative ordered positions of two events depend only on the times of those two events. -/
theorem orderedTwoPointTimedEventPosition_lt_iff_of_eventTime_eq {n : ℕ}
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (a b : TwoPointTimedEvent n)
    (ha : twoPointTimedEventTime τ τ' σ a = twoPointTimedEventTime τ τ' υ a)
    (hb : twoPointTimedEventTime τ τ' σ b = twoPointTimedEventTime τ τ' υ b) :
    (orderedTwoPointTimedEventPosition τ τ' σ a <
        orderedTwoPointTimedEventPosition τ τ' σ b) ↔
      (orderedTwoPointTimedEventPosition τ τ' υ a <
        orderedTwoPointTimedEventPosition τ τ' υ b) := by
  rw [orderedTwoPointTimedEventPosition_lt_iff,
    orderedTwoPointTimedEventPosition_lt_iff]
  unfold twoPointTimedEventBefore
  rw [twoPointTimedEventBeforeOrEqual_congr τ τ' σ υ a b ha hb]

/-- The operator represented by a mixed external/interaction event. -/
noncomputable def twoPointTimedEventOperator {n : ℕ} (ε : Mode → ℝ) (i j : Mode)
    (τ τ' : ℝ) (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    TwoPointTimedEvent n → FockSpace Mode →ₗ[ℂ] FockSpace Mode
  | .inl e => externalFieldOperator ε (twoPointExternalTimes τ τ' e)
      (twoPointExternalLabels i j e)
  | .inr v => interactionPicture ε (quarticVertexOperator (q v)) (σ v)

@[simp]
theorem twoPointTimedEventOperator_external_zero {n : ℕ} (ε : Mode → ℝ) (i j : Mode)
    (τ τ' : ℝ) (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    twoPointTimedEventOperator ε i j τ τ' q σ (Sum.inl 0) =
      externalFieldOperator ε τ (.annihilation i) := by
  simp [twoPointTimedEventOperator]

@[simp]
theorem twoPointTimedEventOperator_external_one {n : ℕ} (ε : Mode → ℝ) (i j : Mode)
    (τ τ' : ℝ) (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    twoPointTimedEventOperator ε i j τ τ' q σ (Sum.inl 1) =
      externalFieldOperator ε τ' (.creation j) := by
  simp [twoPointTimedEventOperator]

@[simp]
theorem twoPointTimedEventOperator_interaction {n : ℕ} (ε : Mode → ℝ) (i j : Mode)
    (τ τ' : ℝ) (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) (v : Fin n) :
    twoPointTimedEventOperator ε i j τ τ' q σ (Sum.inr v) =
      interactionPicture ε (quarticVertexOperator (q v)) (σ v) :=
  rfl

/-- The exchange sign coming from the relative order of the two odd external fields. -/
noncomputable def twoPointExternalOrderSign (τ τ' : ℝ) : ℂ :=
  @ite ℂ (τ < τ') (Classical.propDecidable _)
    (Common.Statistics.fermion.zetaInt : ℂ) 1

/-- The mixed time-ordered operator product of two external fields and `n` quartic interaction
vertices. -/
noncomputable def mixedTimeOrderedVertexComp {n : ℕ} (ε : Mode → ℝ) (i j : Mode)
    (τ τ' : ℝ) (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  twoPointExternalOrderSign τ τ' •
    Common.prodComp ((orderedTwoPointTimedEvents τ τ' σ).map
      (twoPointTimedEventOperator ε i j τ τ' q σ))

set_option linter.unusedSimpArgs false in
private theorem orderedTwoPointTimedEvents_zero_of_gt (σ : Fin 0 → ℝ)
    {τ τ' : ℝ} (h : τ' < τ) :
    orderedTwoPointTimedEvents τ τ' σ =
      [Sum.inl 0, Sum.inl 1] := by
  have hnot : ¬ τ < τ' := not_lt_of_ge h.le
  have hne : τ' ≠ τ := ne_of_lt h
  have hnotle : ¬ τ ≤ τ' := not_le_of_gt h
  simp [orderedTwoPointTimedEvents, sortTwoPointTimedEvents,
    twoPointInteractionEventList, insertTwoPointTimedEvent,
    twoPointTimedEventBeforeOrEqual, twoPointTimedEventTime, twoPointTimedEventRank,
    hnot, hne, hnotle]

set_option linter.unusedSimpArgs false in
private theorem orderedTwoPointTimedEvents_zero_of_lt (σ : Fin 0 → ℝ)
    {τ τ' : ℝ} (h : τ < τ') :
    orderedTwoPointTimedEvents τ τ' σ =
      [Sum.inl 1, Sum.inl 0] := by
  simp [orderedTwoPointTimedEvents, sortTwoPointTimedEvents,
    twoPointInteractionEventList, insertTwoPointTimedEvent,
    twoPointTimedEventBeforeOrEqual, twoPointTimedEventTime, twoPointTimedEventRank,
    h, h.le, h.ne]

/-- At interaction order zero and `τ' < τ`, mixed ordering reduces to the ordinary two-point
ordered product with the annihilation field on the left. -/
theorem mixedTimeOrderedVertexComp_zero_of_gt (ε : Mode → ℝ) (i j : Mode)
    (q : Fin 0 → QuarticVertexLabel Mode) (σ : Fin 0 → ℝ) {τ τ' : ℝ} (h : τ' < τ) :
    mixedTimeOrderedVertexComp ε i j τ τ' q σ =
      twoPointTimeOrderedProduct ε i j τ τ' := by
  rw [twoPointTimeOrderedProduct_of_gt ε i j h, mixedTimeOrderedVertexComp,
    orderedTwoPointTimedEvents_zero_of_gt σ h]
  simp [twoPointExternalOrderSign, not_lt_of_ge h.le, Common.prodComp]

/-- At interaction order zero and `τ < τ'`, mixed ordering reduces to the ordinary two-point
ordered product with the creation field moved left and the fermionic exchange sign. -/
theorem mixedTimeOrderedVertexComp_zero_of_lt (ε : Mode → ℝ) (i j : Mode)
    (q : Fin 0 → QuarticVertexLabel Mode) (σ : Fin 0 → ℝ) {τ τ' : ℝ} (h : τ < τ') :
    mixedTimeOrderedVertexComp ε i j τ τ' q σ =
      twoPointTimeOrderedProduct ε i j τ τ' := by
  rw [twoPointTimeOrderedProduct_of_lt ε i j h, mixedTimeOrderedVertexComp,
    orderedTwoPointTimedEvents_zero_of_lt σ h]
  simp [twoPointExternalOrderSign, h, Common.prodComp]

end Fermionic
end SecondQuantization
