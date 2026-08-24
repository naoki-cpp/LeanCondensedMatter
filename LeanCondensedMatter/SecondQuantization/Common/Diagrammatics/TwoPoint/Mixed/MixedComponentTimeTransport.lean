import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedComponentPosition
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.MixedOrderChamber

set_option linter.style.header false

/-!
# Statistics-independent mixed component time transport

Mixed-time positions belonging to one full two-point diagram component can be compared across two
interaction-time assignments through their common standard component-leg fiber. This module owns the
resulting transport, its coordinate invariance, component-local time equality, and the two structural
conditions used downstream to preserve mixed linear order: equality on the component's interaction
vertices and membership in the same global mixed-order chamber.

No contraction value, Gibbs expectation, exchange sign, or statistics specialization appears here.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*}

/-- Two interaction-time assignments agree on the actual interaction vertices of one full diagram
component. -/
noncomputable def TwoPointDiagram.ComponentTimeEq {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (B : d.componentPartition.parts) (σ υ : Fin n → ℝ) : Prop :=
  ∀ v : Fin n,
    v ∈ TwoPointDiagram.interactionPart
      (B : Finset (TwoPointVertex (Finset.univ : Finset (Fin n)))) →
      σ v = υ v

@[refl]
theorem TwoPointDiagram.componentTimeEq_refl {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (B : d.componentPartition.parts) (σ : Fin n → ℝ) :
    d.ComponentTimeEq B σ σ := by
  intro v hv
  rfl

@[symm]
theorem TwoPointDiagram.ComponentTimeEq.symm {n : ℕ}
    {d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n))}
    {B : d.componentPartition.parts} {σ υ : Fin n → ℝ}
    (h : d.ComponentTimeEq B σ υ) : d.ComponentTimeEq B υ σ := by
  intro v hv
  exact (h v hv).symm

@[trans]
theorem TwoPointDiagram.ComponentTimeEq.trans {n : ℕ}
    {d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n))}
    {B : d.componentPartition.parts} {σ υ ω : Fin n → ℝ}
    (hσυ : d.ComponentTimeEq B σ υ) (hυω : d.ComponentTimeEq B υ ω) :
    d.ComponentTimeEq B σ ω := by
  intro v hv
  exact (hσυ v hv).trans (hυω v hv)

/-- Canonical comparison of mixed positions of one full component at two interaction-time
assignments. The comparison passes through the fixed standard component-leg fiber. -/
noncomputable def TwoPointDiagram.mixedComponentPositionTimeEquiv {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.componentPartition.parts) :
    d.MixedComponentPosition τ τ' σ B ≃ d.MixedComponentPosition τ τ' υ B :=
  (d.mixedComponentPositionEquiv τ τ' σ B).trans
    (d.mixedComponentPositionEquiv τ τ' υ B).symm

@[simp]
theorem TwoPointDiagram.mixedComponentPositionTimeEquiv_refl {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.componentPartition.parts)
    (p : d.MixedComponentPosition τ τ' σ B) :
    d.mixedComponentPositionTimeEquiv τ τ' σ σ B p = p := by
  simp [TwoPointDiagram.mixedComponentPositionTimeEquiv]

@[simp]
theorem TwoPointDiagram.mixedComponentPositionTimeEquiv_symm_apply {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.componentPartition.parts)
    (p : d.MixedComponentPosition τ τ' σ B) :
    d.mixedComponentPositionTimeEquiv τ τ' υ σ B
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p) = p := by
  simp [TwoPointDiagram.mixedComponentPositionTimeEquiv]

/-- Reading the standard component leg after time transport recovers the original standard
component leg. -/
@[simp]
theorem TwoPointDiagram.mixedComponentPositionEquiv_timeEquiv {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.componentPartition.parts)
    (p : d.MixedComponentPosition τ τ' σ B) :
    d.mixedComponentPositionEquiv τ τ' υ B
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p) =
      d.mixedComponentPositionEquiv τ τ' σ B p := by
  simp [TwoPointDiagram.mixedComponentPositionTimeEquiv]

/-- Time transport preserves the underlying position in the standard flattened diagram-leg
enumeration. -/
private theorem TwoPointDiagram.mixedTimeAmbientPositionEquiv_positionTimeEquiv {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.componentPartition.parts)
    (p : d.MixedComponentPosition τ τ' σ B) :
    mixedTimeAmbientPositionEquiv τ τ' υ
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p).1 =
      mixedTimeAmbientPositionEquiv τ τ' σ p.1 := by
  have h := congrArg Subtype.val
    (d.mixedComponentPositionEquiv_timeEquiv τ τ' σ υ B p)
  change mixedTimeAmbientPositionEquiv τ τ' υ
      (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p).1 =
    mixedTimeAmbientPositionEquiv τ τ' σ p.1 at h
  exact h

/-- Time transport preserves the standard atomic leg identity represented by a mixed component
position. -/
theorem TwoPointDiagram.mixedTimeOrderedAtomicLegEquiv_positionTimeEquiv {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.componentPartition.parts)
    (p : d.MixedComponentPosition τ τ' σ B) :
    mixedTimeOrderedAtomicLegEquiv τ τ' υ
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p).1 =
      mixedTimeOrderedAtomicLegEquiv τ τ' σ p.1 := by
  rw [← twoPointLegEquiv_mixedTimeAmbientPositionEquiv,
    ← twoPointLegEquiv_mixedTimeAmbientPositionEquiv]
  exact congrArg (twoPointLegEquiv (Finset.univ : Finset (Fin n)))
    (d.mixedTimeAmbientPositionEquiv_positionTimeEquiv τ τ' σ υ B p)

/-- Under component-local equality of interaction times, the supporting event of every mixed
component position has the same time at both assignments. -/
private theorem TwoPointDiagram.componentPosition_eventTime_eq {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.componentPartition.parts)
    (hTime : d.ComponentTimeEq B σ υ)
    (p : d.MixedComponentPosition τ τ' σ B) :
    twoPointTimedEventTime τ τ' σ
        (orderedTwoPointLegEvent
          (mixedTimeOrderedAtomicLegEquiv τ τ' σ p.1)) =
      twoPointTimedEventTime τ τ' υ
        (orderedTwoPointLegEvent
          (mixedTimeOrderedAtomicLegEquiv τ τ' σ p.1)) := by
  have hAmbient :
      d.legInComponent
        (B : Finset (TwoPointVertex (Finset.univ : Finset (Fin n))))
        (mixedTimeAmbientPositionEquiv τ τ' σ p.1) :=
    (d.mixedPositionComponent_eq_iff_legInComponent τ τ' σ B p.1).1 p.2
  have hUnflattened :=
    (d.legInComponent_iff_unflattened B
      (mixedTimeAmbientPositionEquiv τ τ' σ p.1)).1 hAmbient
  rw [twoPointLegEquiv_mixedTimeAmbientPositionEquiv] at hUnflattened
  generalize hleg : mixedTimeOrderedAtomicLegEquiv τ τ' σ p.1 = leg at hUnflattened ⊢
  cases leg with
  | inl e =>
      simp [orderedTwoPointLegEvent, twoPointTimedEventTime]
  | inr leg =>
      have hvB :
          (Sum.inr leg.1 : TwoPointVertex (Finset.univ : Finset (Fin n))) ∈
            (B : Finset (TwoPointVertex (Finset.univ : Finset (Fin n)))) := by
        simpa [TwoPointDiagram.unflattenedLegInComponent, twoPointLegVertex] using hUnflattened
      have hvPart :
          (leg.1.1 : Fin n) ∈ TwoPointDiagram.interactionPart
            (B : Finset (TwoPointVertex (Finset.univ : Finset (Fin n)))) :=
        (TwoPointDiagram.mem_interactionPart_subtype
          (B : Finset (TwoPointVertex (Finset.univ : Finset (Fin n)))) leg.1).2 hvB
      simpa [orderedTwoPointLegEvent, twoPointTimedEventTime] using
        hTime leg.1.1 hvPart

/-- Component position transport preserves strict mixed order as soon as the flattened atomic-leg
order of the two supporting legs is preserved. This is the coordinate bookkeeping shared by every
sufficient condition for order preservation. -/
private theorem TwoPointDiagram.mixedComponentPositionTimeEquiv_lt_iff_of_legPosition_lt_iff {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.componentPartition.parts)
    (p q : d.MixedComponentPosition τ τ' σ B)
    (hOrder :
      (mixedTimeOrderedAtomicLegPosition τ τ' σ (mixedTimeOrderedAtomicLegEquiv τ τ' σ p.1) <
          mixedTimeOrderedAtomicLegPosition τ τ' σ (mixedTimeOrderedAtomicLegEquiv τ τ' σ q.1)) ↔
        (mixedTimeOrderedAtomicLegPosition τ τ' υ (mixedTimeOrderedAtomicLegEquiv τ τ' σ p.1) <
          mixedTimeOrderedAtomicLegPosition τ τ' υ (mixedTimeOrderedAtomicLegEquiv τ τ' σ q.1))) :
    p.1 < q.1 ↔
      (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p).1 <
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B q).1 := by
  have hpSource :
      mixedTimeOrderedAtomicLegPosition τ τ' σ (mixedTimeOrderedAtomicLegEquiv τ τ' σ p.1) = p.1 :=
    mixedTimeOrderedAtomicLegPosition_mixedTimeOrderedAtomicLegEquiv _ _ _ _
  have hqSource :
      mixedTimeOrderedAtomicLegPosition τ τ' σ (mixedTimeOrderedAtomicLegEquiv τ τ' σ q.1) = q.1 :=
    mixedTimeOrderedAtomicLegPosition_mixedTimeOrderedAtomicLegEquiv _ _ _ _
  have hpTarget :
      mixedTimeOrderedAtomicLegPosition τ τ' υ (mixedTimeOrderedAtomicLegEquiv τ τ' σ p.1) =
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p).1 := by
    rw [← d.mixedTimeOrderedAtomicLegEquiv_positionTimeEquiv τ τ' σ υ B p]
    exact mixedTimeOrderedAtomicLegPosition_mixedTimeOrderedAtomicLegEquiv _ _ _ _
  have hqTarget :
      mixedTimeOrderedAtomicLegPosition τ τ' υ (mixedTimeOrderedAtomicLegEquiv τ τ' σ q.1) =
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B q).1 := by
    rw [← d.mixedTimeOrderedAtomicLegEquiv_positionTimeEquiv τ τ' σ υ B q]
    exact mixedTimeOrderedAtomicLegPosition_mixedTimeOrderedAtomicLegEquiv _ _ _ _
  rw [hpSource, hqSource, hpTarget, hqTarget] at hOrder
  exact hOrder

/-- Component position transport preserves strict mixed order whenever the two assignments agree on
the interaction vertices of that component. -/
theorem TwoPointDiagram.mixedComponentPositionTimeEquiv_lt_iff {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.componentPartition.parts)
    (hTime : d.ComponentTimeEq B σ υ)
    (p q : d.MixedComponentPosition τ τ' σ B) :
    p.1 < q.1 ↔
      (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p).1 <
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B q).1 :=
  d.mixedComponentPositionTimeEquiv_lt_iff_of_legPosition_lt_iff τ τ' σ υ B p q
    (mixedTimeOrderedAtomicLegPosition_lt_iff_of_eventTime_eq τ τ' σ υ _ _
      (d.componentPosition_eventTime_eq τ τ' σ υ B hTime p)
      (d.componentPosition_eventTime_eq τ τ' σ υ B hTime q))

/-- Atomic-leg order is unchanged across assignments in the same mixed-event order chamber. -/
theorem mixedTimeOrderedAtomicLegPosition_lt_iff_of_sameOrderChamber {n : ℕ}
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (x y : OrderedTwoPointLeg n)
    (hChamber : SameTwoPointOrderChamber τ τ' σ υ) :
    (mixedTimeOrderedAtomicLegPosition τ τ' σ x <
        mixedTimeOrderedAtomicLegPosition τ τ' σ y) ↔
      (mixedTimeOrderedAtomicLegPosition τ τ' υ x <
        mixedTimeOrderedAtomicLegPosition τ τ' υ y) :=
  mixedTimeOrderedAtomicLegPosition_lt_iff_of_eventPosition_lt_iff τ τ' σ υ x y
    (orderedTwoPointTimedEventPosition_lt_iff_of_sameOrderChamber
      hChamber (orderedTwoPointLegEvent x) (orderedTwoPointLegEvent y))

/-- Component position transport preserves strict mixed order across assignments in the same global
mixed-order chamber. -/
theorem TwoPointDiagram.mixedComponentPositionTimeEquiv_lt_iff_of_sameOrderChamber {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.componentPartition.parts)
    (hChamber : SameTwoPointOrderChamber τ τ' σ υ)
    (p q : d.MixedComponentPosition τ τ' σ B) :
    p.1 < q.1 ↔
      (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p).1 <
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B q).1 :=
  d.mixedComponentPositionTimeEquiv_lt_iff_of_legPosition_lt_iff τ τ' σ υ B p q
    (mixedTimeOrderedAtomicLegPosition_lt_iff_of_sameOrderChamber τ τ' σ υ _ _ hChamber)

/-- External-component restricted position coordinates are unchanged by time transport. -/
@[simp]
theorem TwoPointDiagram.mixedExternalPositionEquiv_positionTimeEquiv {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ)
    (p : d.MixedComponentPosition τ τ' σ d.externalComponentPart) :
    d.mixedExternalPositionEquiv τ τ' υ
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ d.externalComponentPart p) =
      d.mixedExternalPositionEquiv τ τ' σ p := by
  simp [TwoPointDiagram.mixedExternalPositionEquiv,
    TwoPointDiagram.mixedComponentPositionTimeEquiv]

/-- Vacuum-component restricted position coordinates are unchanged by time transport. -/
@[simp]
theorem TwoPointDiagram.mixedVacuumPositionEquiv_positionTimeEquiv {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.componentPartition.parts)
    (hVac : d.ComponentIsVacuum B)
    (p : d.MixedComponentPosition τ τ' σ B) :
    d.mixedVacuumPositionEquiv τ τ' υ B hVac
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p) =
      d.mixedVacuumPositionEquiv τ τ' σ B hVac p := by
  simp [TwoPointDiagram.mixedVacuumPositionEquiv,
    TwoPointDiagram.mixedComponentPositionTimeEquiv]

end Common
end SecondQuantization