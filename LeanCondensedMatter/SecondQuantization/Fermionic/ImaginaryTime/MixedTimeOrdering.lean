import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized.PeelFirst
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.QuarticInteraction
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.ExternalField
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.InteractionPicture

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

/-- The interaction events in their canonical supplied slot order. -/
def twoPointInteractionEventList (n : ℕ) : List (TwoPointTimedEvent n) :=
  List.ofFn fun v : Fin n => Sum.inr v

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
