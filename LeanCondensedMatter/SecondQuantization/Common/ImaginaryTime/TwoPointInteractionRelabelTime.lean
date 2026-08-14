import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.TwoPointInteractionRelabel

set_option linter.style.header false

/-!
# Mixed-time event transport under interaction-slot relabeling

An interaction-slot permutation fixes the two external events and transports each interaction event
to the old slot whose data it inherits. If the old time assignment is precomposed by the inverse
slot permutation, corresponding events have exactly the same imaginary time.

This is statistics-independent order structure; operator exchange signs belong to the specialized
realization layers.
-/

namespace SecondQuantization
namespace Common

/-- Relabel mixed two-point events by an interaction-slot permutation, fixing the external events.
The permutation maps a new interaction event to the old event whose data it inherits. -/
def interactionVertexEventRelabel {n : ℕ} (π : Equiv.Perm (Fin n)) :
    TwoPointTimedEvent n ≃ TwoPointTimedEvent n where
  toFun
    | Sum.inl e => Sum.inl e
    | Sum.inr v => Sum.inr (π v)
  invFun
    | Sum.inl e => Sum.inl e
    | Sum.inr v => Sum.inr (π.symm v)
  left_inv event := by
    rcases event with e | v
    · rfl
    · simp
  right_inv event := by
    rcases event with e | v
    · rfl
    · simp

@[simp]
theorem interactionVertexEventRelabel_external {n : ℕ} (π : Equiv.Perm (Fin n)) (e : Fin 2) :
    interactionVertexEventRelabel π (Sum.inl e) = (Sum.inl e : TwoPointTimedEvent n) :=
  rfl

@[simp]
theorem interactionVertexEventRelabel_interaction {n : ℕ} (π : Equiv.Perm (Fin n))
    (v : Fin n) :
    interactionVertexEventRelabel π (Sum.inr v) =
      (Sum.inr (π v) : TwoPointTimedEvent n) :=
  rfl

/-- Relabeling a standard two-point leg transports its supporting mixed event by the same slot
permutation. -/
@[simp]
theorem orderedTwoPointLegEvent_interactionVertexLegRelabel {n : ℕ}
    (π : Equiv.Perm (Fin n)) (leg : OrderedTwoPointLeg n) :
    orderedTwoPointLegEvent (interactionVertexLegRelabel π leg) =
      interactionVertexEventRelabel π (orderedTwoPointLegEvent leg) := by
  rcases leg with e | ⟨v, l⟩
  · rfl
  · rfl

/-- Corresponding events have the same physical imaginary time when the old time assignment is
precomposed by the inverse interaction-slot permutation. -/
@[simp]
theorem twoPointTimedEventTime_interactionVertexEventRelabel {n : ℕ}
    (π : Equiv.Perm (Fin n)) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (event : TwoPointTimedEvent n) :
    twoPointTimedEventTime τ τ' (fun v => σ (π.symm v))
        (interactionVertexEventRelabel π event) =
      twoPointTimedEventTime τ τ' σ event := by
  rcases event with e | v
  · rfl
  · simp [interactionVertexEventRelabel, twoPointTimedEventTime]

/-- The same time-covariance statement expressed on the event supporting a standard two-point leg. -/
theorem twoPointTimedEventTime_orderedTwoPointLegEvent_interactionVertexLegRelabel {n : ℕ}
    (π : Equiv.Perm (Fin n)) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (leg : OrderedTwoPointLeg n) :
    twoPointTimedEventTime τ τ' (fun v => σ (π.symm v))
        (orderedTwoPointLegEvent (interactionVertexLegRelabel π leg)) =
      twoPointTimedEventTime τ τ' σ (orderedTwoPointLegEvent leg) := by
  rw [orderedTwoPointLegEvent_interactionVertexLegRelabel,
    twoPointTimedEventTime_interactionVertexEventRelabel]

/-- If two event times are distinct, stable tie-breaking is irrelevant and mixed-event precedence
is equivariant under interaction-slot relabeling. -/
theorem twoPointTimedEventBeforeOrEqual_interactionVertexEventRelabel_iff_of_time_ne {n : ℕ}
    (π : Equiv.Perm (Fin n)) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (a b : TwoPointTimedEvent n)
    (hTime : twoPointTimedEventTime τ τ' σ a ≠ twoPointTimedEventTime τ τ' σ b) :
    twoPointTimedEventBeforeOrEqual τ τ' (fun v => σ (π.symm v))
        (interactionVertexEventRelabel π a) (interactionVertexEventRelabel π b) ↔
      twoPointTimedEventBeforeOrEqual τ τ' σ a b := by
  simp only [twoPointTimedEventBeforeOrEqual,
    twoPointTimedEventTime_interactionVertexEventRelabel]
  simp [hTime]

/-- Strict mixed-event precedence is likewise equivariant for distinct event times. -/
theorem twoPointTimedEventBefore_interactionVertexEventRelabel_iff_of_time_ne {n : ℕ}
    (π : Equiv.Perm (Fin n)) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (a b : TwoPointTimedEvent n)
    (hTime : twoPointTimedEventTime τ τ' σ a ≠ twoPointTimedEventTime τ τ' σ b) :
    twoPointTimedEventBefore τ τ' (fun v => σ (π.symm v))
        (interactionVertexEventRelabel π a) (interactionVertexEventRelabel π b) ↔
      twoPointTimedEventBefore τ τ' σ a b := by
  rw [twoPointTimedEventBefore, twoPointTimedEventBefore]
  rw [twoPointTimedEventBeforeOrEqual_interactionVertexEventRelabel_iff_of_time_ne
    π τ τ' σ a b hTime]
  exact and_congr_right (fun _ => (interactionVertexEventRelabel π).injective.ne_iff)

/-- If the interaction-time assignment is injective, relabeling preserves stable precedence for
all events. Equal-time external/interaction pairs keep the same external-before-interaction rank,
while two distinct interaction events cannot tie. -/
theorem twoPointTimedEventBeforeOrEqual_interactionVertexEventRelabel_iff_of_injective {n : ℕ}
    (π : Equiv.Perm (Fin n)) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : Function.Injective σ) (a b : TwoPointTimedEvent n) :
    twoPointTimedEventBeforeOrEqual τ τ' (fun v => σ (π.symm v))
        (interactionVertexEventRelabel π a) (interactionVertexEventRelabel π b) ↔
      twoPointTimedEventBeforeOrEqual τ τ' σ a b := by
  by_cases hTime :
      twoPointTimedEventTime τ τ' σ a ≠ twoPointTimedEventTime τ τ' σ b
  · exact twoPointTimedEventBeforeOrEqual_interactionVertexEventRelabel_iff_of_time_ne
      π τ τ' σ a b hTime
  · have hEq :
        twoPointTimedEventTime τ τ' σ a = twoPointTimedEventTime τ τ' σ b :=
      not_ne_iff.mp hTime
    rcases a with a | a
    · rcases b with b | b
      · rfl
      · have hEqNew :
            twoPointTimedEventTime τ τ' (fun v => σ (π.symm v))
                (interactionVertexEventRelabel π (Sum.inl a)) =
              twoPointTimedEventTime τ τ' (fun v => σ (π.symm v))
                (interactionVertexEventRelabel π (Sum.inr b)) := by
          rw [twoPointTimedEventTime_interactionVertexEventRelabel,
            twoPointTimedEventTime_interactionVertexEventRelabel]
          exact hEq
        have hRankOld :
            twoPointTimedEventRank (Sum.inl a : TwoPointTimedEvent n) ≤
              twoPointTimedEventRank (Sum.inr b) := by
          change (a : ℕ) ≤ 2 + (b : ℕ)
          omega
        have hRankNew :
            twoPointTimedEventRank (interactionVertexEventRelabel π (Sum.inl a)) ≤
              twoPointTimedEventRank (interactionVertexEventRelabel π (Sum.inr b)) := by
          simp only [interactionVertexEventRelabel_external, interactionVertexEventRelabel_interaction]
          change (a : ℕ) ≤ 2 + ((π b : Fin n) : ℕ)
          omega
        rw [twoPointTimedEventBeforeOrEqual, twoPointTimedEventBeforeOrEqual]
        constructor
        · intro _
          exact Or.inr ⟨hEq, hRankOld⟩
        · intro _
          exact Or.inr ⟨hEqNew, hRankNew⟩
    · rcases b with b | b
      · have hEqNew :
            twoPointTimedEventTime τ τ' (fun v => σ (π.symm v))
                (interactionVertexEventRelabel π (Sum.inr a)) =
              twoPointTimedEventTime τ τ' (fun v => σ (π.symm v))
                (interactionVertexEventRelabel π (Sum.inl b)) := by
          rw [twoPointTimedEventTime_interactionVertexEventRelabel,
            twoPointTimedEventTime_interactionVertexEventRelabel]
          exact hEq
        have hRankOld :
            twoPointTimedEventRank (Sum.inl b : TwoPointTimedEvent n) <
              twoPointTimedEventRank (Sum.inr a) := by
          change (b : ℕ) < 2 + (a : ℕ)
          omega
        have hRankNew :
            twoPointTimedEventRank (interactionVertexEventRelabel π (Sum.inl b)) <
              twoPointTimedEventRank (interactionVertexEventRelabel π (Sum.inr a)) := by
          simp only [interactionVertexEventRelabel_external, interactionVertexEventRelabel_interaction]
          change (b : ℕ) < 2 + ((π a : Fin n) : ℕ)
          omega
        rw [twoPointTimedEventBeforeOrEqual, twoPointTimedEventBeforeOrEqual]
        constructor
        · intro h
          rcases h with hlt | ⟨_, hle⟩
          · rw [hEqNew] at hlt
            exact (lt_irrefl _ hlt).elim
          · exact (not_le_of_gt hRankNew hle).elim
        · intro h
          rcases h with hlt | ⟨_, hle⟩
          · rw [hEq] at hlt
            exact (lt_irrefl _ hlt).elim
          · exact (not_le_of_gt hRankOld hle).elim
      · have hab : a = b := hσ (by simpa [twoPointTimedEventTime] using hEq)
        subst b
        simp [twoPointTimedEventBeforeOrEqual, twoPointTimedEventRank]

/-- Under an injective interaction-time assignment, strict event precedence is fully equivariant
under interaction-slot relabeling. -/
theorem twoPointTimedEventBefore_interactionVertexEventRelabel_iff_of_injective {n : ℕ}
    (π : Equiv.Perm (Fin n)) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : Function.Injective σ) (a b : TwoPointTimedEvent n) :
    twoPointTimedEventBefore τ τ' (fun v => σ (π.symm v))
        (interactionVertexEventRelabel π a) (interactionVertexEventRelabel π b) ↔
      twoPointTimedEventBefore τ τ' σ a b := by
  rw [twoPointTimedEventBefore, twoPointTimedEventBefore]
  rw [twoPointTimedEventBeforeOrEqual_interactionVertexEventRelabel_iff_of_injective
    π τ τ' σ hσ a b]
  exact and_congr_right (fun _ => (interactionVertexEventRelabel π).injective.ne_iff)

/-- Under an injective interaction-time assignment, the time-ordered event positions are transported
order-equivariantly by interaction-slot relabeling. -/
theorem orderedTwoPointTimedEventPosition_interactionVertexEventRelabel_lt_iff_of_injective
    {n : ℕ} (π : Equiv.Perm (Fin n)) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : Function.Injective σ) (a b : TwoPointTimedEvent n) :
    orderedTwoPointTimedEventPosition τ τ' (fun v => σ (π.symm v))
        (interactionVertexEventRelabel π a) <
      orderedTwoPointTimedEventPosition τ τ' (fun v => σ (π.symm v))
        (interactionVertexEventRelabel π b) ↔
      orderedTwoPointTimedEventPosition τ τ' σ a <
        orderedTwoPointTimedEventPosition τ τ' σ b := by
  rw [orderedTwoPointTimedEventPosition_lt_iff, orderedTwoPointTimedEventPosition_lt_iff]
  exact twoPointTimedEventBefore_interactionVertexEventRelabel_iff_of_injective
    π τ τ' σ hσ a b

end Common
end SecondQuantization
