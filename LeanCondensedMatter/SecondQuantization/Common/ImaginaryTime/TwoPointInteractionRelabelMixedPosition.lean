import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.TwoPointInteractionRelabelTime
import Mathlib.Order.Preorder.Finite
import Mathlib.Order.WellFounded

set_option linter.style.header false

/-!
# Mixed atomic positions under interaction-slot relabeling

For a relabeled two-point structure, a new interaction slot `v` inherits the old slot `π v`. At a
fixed new time assignment `σ`, the corresponding old time assignment is
`fun v => σ (π.symm v)`.

The induced mixed-position permutation is purely combinatorial and independent of operator
realization or particle statistics.
-/

namespace SecondQuantization
namespace Common

/-- The permutation from mixed atomic positions at time assignment `σ` to mixed atomic positions at
the corresponding assignment `fun v => σ (π.symm v)`. -/
noncomputable def interactionVertexMixedPositionRelabel {n : ℕ}
    (π : Equiv.Perm (Fin n)) (τ τ' : ℝ) (σ : Fin n → ℝ) :
    Equiv.Perm (Fin (2 * (2 * n + 1))) :=
  (mixedTimeOrderedAtomicLegEquiv τ τ' σ).trans
    ((interactionVertexLegRelabel π).trans
      (mixedTimeOrderedAtomicLegEquiv τ τ' (fun v => σ (π.symm v))).symm)

/-- Reading the old standard leg at a transported mixed position gives the relabeling of the new
standard leg. -/
@[simp]
theorem mixedTimeOrderedAtomicLegEquiv_interactionVertexMixedPositionRelabel {n : ℕ}
    (π : Equiv.Perm (Fin n)) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (p : Fin (2 * (2 * n + 1))) :
    mixedTimeOrderedAtomicLegEquiv τ τ' (fun v => σ (π.symm v))
        (interactionVertexMixedPositionRelabel π τ τ' σ p) =
      interactionVertexLegRelabel π (mixedTimeOrderedAtomicLegEquiv τ τ' σ p) := by
  simp [interactionVertexMixedPositionRelabel]

/-- The transported mixed position is exactly the old mixed position of the relabeled standard
leg. -/
theorem interactionVertexMixedPositionRelabel_apply {n : ℕ}
    (π : Equiv.Perm (Fin n)) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (p : Fin (2 * (2 * n + 1))) :
    interactionVertexMixedPositionRelabel π τ τ' σ p =
      mixedTimeOrderedAtomicLegPosition τ τ' (fun v => σ (π.symm v))
        (interactionVertexLegRelabel π (mixedTimeOrderedAtomicLegEquiv τ τ' σ p)) := by
  apply (mixedTimeOrderedAtomicLegEquiv τ τ' (fun v => σ (π.symm v))).injective
  rw [mixedTimeOrderedAtomicLegEquiv_interactionVertexMixedPositionRelabel,
    mixedTimeOrderedAtomicLegEquiv_mixedTimeOrderedAtomicLegPosition]

/-- The supporting old event of a transported mixed position is the relabeling of the supporting
new event. -/
theorem orderedTwoPointLegEvent_interactionVertexMixedPositionRelabel {n : ℕ}
    (π : Equiv.Perm (Fin n)) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (p : Fin (2 * (2 * n + 1))) :
    orderedTwoPointLegEvent
        (mixedTimeOrderedAtomicLegEquiv τ τ' (fun v => σ (π.symm v))
          (interactionVertexMixedPositionRelabel π τ τ' σ p)) =
      interactionVertexEventRelabel π
        (orderedTwoPointLegEvent (mixedTimeOrderedAtomicLegEquiv τ τ' σ p)) := by
  rw [mixedTimeOrderedAtomicLegEquiv_interactionVertexMixedPositionRelabel]
  exact orderedTwoPointLegEvent_interactionVertexLegRelabel π
    (mixedTimeOrderedAtomicLegEquiv τ τ' σ p)

/-- Transporting a mixed atomic position preserves the physical time of its supporting event. -/
theorem twoPointTimedEventTime_interactionVertexMixedPositionRelabel {n : ℕ}
    (π : Equiv.Perm (Fin n)) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (p : Fin (2 * (2 * n + 1))) :
    twoPointTimedEventTime τ τ' (fun v => σ (π.symm v))
        (orderedTwoPointLegEvent
          (mixedTimeOrderedAtomicLegEquiv τ τ' (fun v => σ (π.symm v))
            (interactionVertexMixedPositionRelabel π τ τ' σ p))) =
      twoPointTimedEventTime τ τ' σ
        (orderedTwoPointLegEvent (mixedTimeOrderedAtomicLegEquiv τ τ' σ p)) := by
  rw [orderedTwoPointLegEvent_interactionVertexMixedPositionRelabel]
  exact twoPointTimedEventTime_interactionVertexEventRelabel π τ τ' σ
    (orderedTwoPointLegEvent (mixedTimeOrderedAtomicLegEquiv τ τ' σ p))

/-- For two positions supported on events at distinct physical times, interaction-slot relabeling
preserves their mixed-order comparison. -/
theorem interactionVertexMixedPositionRelabel_lt_iff_of_eventTime_ne {n : ℕ}
    (π : Equiv.Perm (Fin n)) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (p q : Fin (2 * (2 * n + 1)))
    (hTime :
      twoPointTimedEventTime τ τ' σ
          (orderedTwoPointLegEvent (mixedTimeOrderedAtomicLegEquiv τ τ' σ p)) ≠
        twoPointTimedEventTime τ τ' σ
          (orderedTwoPointLegEvent (mixedTimeOrderedAtomicLegEquiv τ τ' σ q))) :
    (interactionVertexMixedPositionRelabel π τ τ' σ p <
        interactionVertexMixedPositionRelabel π τ τ' σ q) ↔ p < q := by
  let x := mixedTimeOrderedAtomicLegEquiv τ τ' σ p
  let y := mixedTimeOrderedAtomicLegEquiv τ τ' σ q
  have hxy : orderedTwoPointLegEvent x ≠ orderedTwoPointLegEvent y := by
    intro h
    apply hTime
    simpa [x, y, h]
  have hRelabeledXY :
      orderedTwoPointLegEvent (interactionVertexLegRelabel π x) ≠
        orderedTwoPointLegEvent (interactionVertexLegRelabel π y) := by
    simpa [orderedTwoPointLegEvent_interactionVertexLegRelabel] using
      (interactionVertexEventRelabel π).injective.ne hxy
  rw [interactionVertexMixedPositionRelabel_apply,
    interactionVertexMixedPositionRelabel_apply]
  rw [mixedTimeOrderedAtomicLegPosition_lt_iff_eventPosition_lt
    τ τ' (fun v => σ (π.symm v))
    (interactionVertexLegRelabel π x) (interactionVertexLegRelabel π y) hRelabeledXY]
  rw [orderedTwoPointTimedEventPosition_lt_iff]
  rw [orderedTwoPointLegEvent_interactionVertexLegRelabel,
    orderedTwoPointLegEvent_interactionVertexLegRelabel]
  rw [twoPointTimedEventBefore_interactionVertexEventRelabel_iff_of_time_ne
    π τ τ' σ (orderedTwoPointLegEvent x) (orderedTwoPointLegEvent y)]
  · rw [← orderedTwoPointTimedEventPosition_lt_iff]
    rw [← mixedTimeOrderedAtomicLegPosition_lt_iff_eventPosition_lt τ τ' σ x y hxy]
    simpa only [x, y, mixedTimeOrderedAtomicLegPosition_mixedTimeOrderedAtomicLegEquiv]
  · simpa [x, y] using hTime

/-- With injective interaction times, transported mixed positions preserve order whenever their
supporting events are distinct. -/
theorem interactionVertexMixedPositionRelabel_lt_iff_of_injective_of_event_ne {n : ℕ}
    (π : Equiv.Perm (Fin n)) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : Function.Injective σ) (p q : Fin (2 * (2 * n + 1)))
    (hEvent :
      orderedTwoPointLegEvent (mixedTimeOrderedAtomicLegEquiv τ τ' σ p) ≠
        orderedTwoPointLegEvent (mixedTimeOrderedAtomicLegEquiv τ τ' σ q)) :
    (interactionVertexMixedPositionRelabel π τ τ' σ p <
        interactionVertexMixedPositionRelabel π τ τ' σ q) ↔ p < q := by
  let x := mixedTimeOrderedAtomicLegEquiv τ τ' σ p
  let y := mixedTimeOrderedAtomicLegEquiv τ τ' σ q
  have hRelabeledXY :
      orderedTwoPointLegEvent (interactionVertexLegRelabel π x) ≠
        orderedTwoPointLegEvent (interactionVertexLegRelabel π y) := by
    simpa [orderedTwoPointLegEvent_interactionVertexLegRelabel] using
      (interactionVertexEventRelabel π).injective.ne hEvent
  rw [interactionVertexMixedPositionRelabel_apply,
    interactionVertexMixedPositionRelabel_apply]
  rw [mixedTimeOrderedAtomicLegPosition_lt_iff_eventPosition_lt
    τ τ' (fun v => σ (π.symm v))
    (interactionVertexLegRelabel π x) (interactionVertexLegRelabel π y) hRelabeledXY]
  rw [orderedTwoPointLegEvent_interactionVertexLegRelabel,
    orderedTwoPointLegEvent_interactionVertexLegRelabel]
  rw [orderedTwoPointTimedEventPosition_interactionVertexEventRelabel_lt_iff_of_injective
    π τ τ' σ hσ (orderedTwoPointLegEvent x) (orderedTwoPointLegEvent y)]
  rw [← mixedTimeOrderedAtomicLegPosition_lt_iff_eventPosition_lt τ τ' σ x y hEvent]
  simpa only [x, y, mixedTimeOrderedAtomicLegPosition_mixedTimeOrderedAtomicLegEquiv]

private theorem mixedTimeOrderedAtomicLegPosition_lt_iff_eventBlockIdxOf_lt {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) (x y : OrderedTwoPointLeg n)
    (hEvent : orderedTwoPointLegEvent x = orderedTwoPointLegEvent y) :
    (mixedTimeOrderedAtomicLegPosition τ τ' σ x <
        mixedTimeOrderedAtomicLegPosition τ τ' σ y) ↔
      @List.idxOf (OrderedTwoPointLeg n) instBEqOfDecidableEq x
          (twoPointTimedEventAtomicLegs (orderedTwoPointLegEvent x)) <
        @List.idxOf (OrderedTwoPointLeg n) instBEqOfDecidableEq y
          (twoPointTimedEventAtomicLegs (orderedTwoPointLegEvent x)) := by
  classical
  letI : BEq (OrderedTwoPointLeg n) := instBEqOfDecidableEq
  let event := orderedTwoPointLegEvent x
  have hx : x ∈ twoPointTimedEventAtomicLegs event := by
    simpa [event] using orderedTwoPointLeg_mem_eventAtomicLegs x
  have hy : y ∈ twoPointTimedEventAtomicLegs event := by
    simpa [event, hEvent] using orderedTwoPointLeg_mem_eventAtomicLegs y
  have h := List.idxOf_flatMap_block_lt_iff twoPointTimedEventAtomicLegs
    (orderedTwoPointTimedEvents τ τ' σ) event x y
    (mixedTimeOrderedAtomicLegs_nodup τ τ' σ)
    (orderedTwoPointTimedEvents_all_mem τ τ' σ event) hx hy
  simpa [event, mixedTimeOrderedAtomicLegPosition, mixedTimeOrderedAtomicLegEquiv,
    mixedTimeOrderedAtomicLegs, List.Nodup.getEquivOfForallMemList] using h

private theorem twoPointTimedEventAtomicLegs_idxOf_interactionVertexLegRelabel {n : ℕ}
    (π : Equiv.Perm (Fin n)) (leg : OrderedTwoPointLeg n) :
    @List.idxOf (OrderedTwoPointLeg n) instBEqOfDecidableEq
      (interactionVertexLegRelabel π leg)
      (twoPointTimedEventAtomicLegs
        (orderedTwoPointLegEvent (interactionVertexLegRelabel π leg))) =
    @List.idxOf (OrderedTwoPointLeg n) instBEqOfDecidableEq leg
      (twoPointTimedEventAtomicLegs (orderedTwoPointLegEvent leg)) := by
  classical
  letI : BEq (OrderedTwoPointLeg n) := instBEqOfDecidableEq
  rcases leg with e | ⟨⟨v, hv⟩, l⟩
  · simp [interactionVertexLegRelabel, orderedTwoPointLegEvent]
  · fin_cases l <;>
      simp [interactionVertexLegRelabel, orderedTwoPointLegEvent,
        twoPointTimedEventAtomicLegs]

/-- With injective interaction times, the mixed atomic position relabeling preserves the full strict
order, including pairs of legs inside the same quartic interaction block. -/
theorem interactionVertexMixedPositionRelabel_lt_iff_of_injective {n : ℕ}
    (π : Equiv.Perm (Fin n)) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : Function.Injective σ) (p q : Fin (2 * (2 * n + 1))) :
    (interactionVertexMixedPositionRelabel π τ τ' σ p <
        interactionVertexMixedPositionRelabel π τ τ' σ q) ↔ p < q := by
  let x := mixedTimeOrderedAtomicLegEquiv τ τ' σ p
  let y := mixedTimeOrderedAtomicLegEquiv τ τ' σ q
  by_cases hEvent : orderedTwoPointLegEvent x ≠ orderedTwoPointLegEvent y
  · exact interactionVertexMixedPositionRelabel_lt_iff_of_injective_of_event_ne
      π τ τ' σ hσ p q (by simpa [x, y] using hEvent)
  · have hEventEq : orderedTwoPointLegEvent x = orderedTwoPointLegEvent y :=
      not_ne_iff.mp hEvent
    have hRelabeledEvent :
        orderedTwoPointLegEvent (interactionVertexLegRelabel π x) =
          orderedTwoPointLegEvent (interactionVertexLegRelabel π y) := by
      rw [orderedTwoPointLegEvent_interactionVertexLegRelabel,
        orderedTwoPointLegEvent_interactionVertexLegRelabel]
      exact congrArg (interactionVertexEventRelabel π) hEventEq
    rw [interactionVertexMixedPositionRelabel_apply,
      interactionVertexMixedPositionRelabel_apply]
    have hp : mixedTimeOrderedAtomicLegPosition τ τ' σ x = p := by
      simpa only [x] using
        mixedTimeOrderedAtomicLegPosition_mixedTimeOrderedAtomicLegEquiv τ τ' σ p
    have hq : mixedTimeOrderedAtomicLegPosition τ τ' σ y = q := by
      simpa only [y] using
        mixedTimeOrderedAtomicLegPosition_mixedTimeOrderedAtomicLegEquiv τ τ' σ q
    rw [← hp, ← hq]
    have hxinv :
        mixedTimeOrderedAtomicLegEquiv τ τ' σ
            (mixedTimeOrderedAtomicLegPosition τ τ' σ x) = x :=
      mixedTimeOrderedAtomicLegEquiv_mixedTimeOrderedAtomicLegPosition τ τ' σ x
    have hyinv :
        mixedTimeOrderedAtomicLegEquiv τ τ' σ
            (mixedTimeOrderedAtomicLegPosition τ τ' σ y) = y :=
      mixedTimeOrderedAtomicLegEquiv_mixedTimeOrderedAtomicLegPosition τ τ' σ y
    simp only [hxinv, hyinv]
    rw [mixedTimeOrderedAtomicLegPosition_lt_iff_eventBlockIdxOf_lt
      τ τ' (fun v => σ (π.symm v))
      (interactionVertexLegRelabel π x) (interactionVertexLegRelabel π y) hRelabeledEvent]
    rw [mixedTimeOrderedAtomicLegPosition_lt_iff_eventBlockIdxOf_lt
      τ τ' σ x y hEventEq]
    rw [twoPointTimedEventAtomicLegs_idxOf_interactionVertexLegRelabel π x]
    rw [hRelabeledEvent]
    rw [twoPointTimedEventAtomicLegs_idxOf_interactionVertexLegRelabel π y]
    rw [← hEventEq]

/-- The mixed atomic position relabeling is strictly monotone away from interaction-time diagonals. -/
theorem interactionVertexMixedPositionRelabel_strictMono_of_injective {n : ℕ}
    (π : Equiv.Perm (Fin n)) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : Function.Injective σ) :
    StrictMono (interactionVertexMixedPositionRelabel π τ τ' σ) := by
  intro p q hpq
  exact (interactionVertexMixedPositionRelabel_lt_iff_of_injective
    π τ τ' σ hσ p q).2 hpq

/-- A strictly monotone self-permutation of the finite mixed-position order is the identity. -/
@[simp]
theorem interactionVertexMixedPositionRelabel_apply_eq_of_injective {n : ℕ}
    (π : Equiv.Perm (Fin n)) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : Function.Injective σ) (p : Fin (2 * (2 * n + 1))) :
    interactionVertexMixedPositionRelabel π τ τ' σ p = p := by
  have hmono := interactionVertexMixedPositionRelabel_strictMono_of_injective π τ τ' σ hσ
  exact le_antisymm (StrictMono.apply_le hmono) (StrictMono.le_apply hmono)

/-- On injective interaction-time assignments the induced mixed-position permutation is exactly the
identity permutation. -/
theorem interactionVertexMixedPositionRelabel_eq_refl_of_injective {n : ℕ}
    (π : Equiv.Perm (Fin n)) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : Function.Injective σ) :
    interactionVertexMixedPositionRelabel π τ τ' σ = Equiv.refl _ := by
  apply Equiv.ext
  intro p
  exact interactionVertexMixedPositionRelabel_apply_eq_of_injective π τ τ' σ hσ p

end Common
end SecondQuantization
