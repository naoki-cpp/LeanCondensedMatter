import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.InteractionVertexRelabel
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedEventBlockOrder

set_option linter.style.header false

/-!
# Mixed-time event transport under interaction-vertex relabeling

An interaction-slot permutation fixes the two external events and transports each interaction event
to the old slot whose diagram data it inherits.  If the old time assignment is precomposed by the
inverse slot permutation, corresponding events have exactly the same imaginary time.

The stable equal-time rank is intentionally not claimed to be preserved: interaction events use
their slot index as the tie-break rank.  Away from equal-time event pairs, however, mixed-event
precedence is equivariant under interaction-slot relabeling.  This isolates the remaining
fixed-time amplitude covariance obstruction to equal-time block ordering and its fermionic parity.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*}

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

/-- The same time-covariance statement expressed on the event supporting a standard two-point leg.
-/
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

end Fermionic
end SecondQuantization
