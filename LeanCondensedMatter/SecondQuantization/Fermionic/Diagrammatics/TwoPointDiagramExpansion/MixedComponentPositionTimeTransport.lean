import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentPairEquiv
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedPositionLeg

set_option linter.style.header false

/-!
# Transporting mixed component positions across interaction-time assignments

The mixed-time atomic position occupied by a fixed diagram leg depends on the complete interaction-
time assignment. Positions belonging to one full component can nevertheless be compared canonically
by transporting them through the time-independent standard component-leg fiber.

This file defines that transport, proves that it preserves the underlying standard ambient position
and atomic leg identity, and identifies the time-locality condition under which it also preserves the
mixed linear order. The external and vacuum restricted position coordinates are preserved as well.
These statements are the common coordinate layer needed to prove locality of component-internal
crossings and finite Gibbs pair contractions.
-/

namespace SecondQuantization
namespace Fermionic

open Common

variable {Mode : Type*}

/-- Two interaction-time assignments agree on the actual interaction vertices of one full diagram
component. -/
noncomputable def FixedExternalTwoPointWickDiagram.ComponentTimeEq
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (B : d.1.componentPartition.parts) (σ υ : Fin n → ℝ) : Prop :=
  ∀ v : Fin n,
    v ∈ Common.TwoPointDiagram.interactionPart
      (B : Finset (Common.TwoPointVertex
        (Finset.univ : Finset (Fin n)))) →
      σ v = υ v

@[refl]
theorem FixedExternalTwoPointWickDiagram.componentTimeEq_refl
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (B : d.1.componentPartition.parts) (σ : Fin n → ℝ) :
    d.ComponentTimeEq B σ σ := by
  intro v hv
  rfl

@[symm]
theorem FixedExternalTwoPointWickDiagram.ComponentTimeEq.symm
    {n : ℕ} {i j : Mode} {d : FixedExternalTwoPointWickDiagram Mode n i j}
    {B : d.1.componentPartition.parts} {σ υ : Fin n → ℝ}
    (h : d.ComponentTimeEq B σ υ) : d.ComponentTimeEq B υ σ := by
  intro v hv
  exact (h v hv).symm

@[trans]
theorem FixedExternalTwoPointWickDiagram.ComponentTimeEq.trans
    {n : ℕ} {i j : Mode} {d : FixedExternalTwoPointWickDiagram Mode n i j}
    {B : d.1.componentPartition.parts} {σ υ ω : Fin n → ℝ}
    (hσυ : d.ComponentTimeEq B σ υ) (hυω : d.ComponentTimeEq B υ ω) :
    d.ComponentTimeEq B σ ω := by
  intro v hv
  exact (hσυ v hv).trans (hυω v hv)

/-- Canonical comparison of mixed positions of one full component at two interaction-time
assignments. The comparison passes through the fixed standard component-leg fiber. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedComponentPositionTimeEquiv
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.1.componentPartition.parts) :
    d.MixedComponentPosition τ τ' σ B ≃ d.MixedComponentPosition τ τ' υ B :=
  (d.mixedComponentPositionEquiv τ τ' σ B).trans
    (d.mixedComponentPositionEquiv τ τ' υ B).symm

@[simp]
theorem FixedExternalTwoPointWickDiagram.mixedComponentPositionTimeEquiv_refl
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.1.componentPartition.parts)
    (p : d.MixedComponentPosition τ τ' σ B) :
    d.mixedComponentPositionTimeEquiv τ τ' σ σ B p = p := by
  simp [FixedExternalTwoPointWickDiagram.mixedComponentPositionTimeEquiv]

@[simp]
theorem FixedExternalTwoPointWickDiagram.mixedComponentPositionTimeEquiv_symm_apply
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.1.componentPartition.parts)
    (p : d.MixedComponentPosition τ τ' σ B) :
    d.mixedComponentPositionTimeEquiv τ τ' υ σ B
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p) = p := by
  simp [FixedExternalTwoPointWickDiagram.mixedComponentPositionTimeEquiv]

/-- Reading the standard component leg after time transport recovers the original standard
component leg. -/
@[simp]
theorem FixedExternalTwoPointWickDiagram.mixedComponentPositionEquiv_timeEquiv
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.1.componentPartition.parts)
    (p : d.MixedComponentPosition τ τ' σ B) :
    d.mixedComponentPositionEquiv τ τ' υ B
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p) =
      d.mixedComponentPositionEquiv τ τ' σ B p := by
  simp [FixedExternalTwoPointWickDiagram.mixedComponentPositionTimeEquiv]

/-- Time transport preserves the underlying position in the standard flattened diagram-leg
enumeration. -/
theorem FixedExternalTwoPointWickDiagram.mixedTimeAmbientPositionEquiv_positionTimeEquiv
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.1.componentPartition.parts)
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
theorem FixedExternalTwoPointWickDiagram.mixedTimeOrderedAtomicLegEquiv_positionTimeEquiv
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.1.componentPartition.parts)
    (p : d.MixedComponentPosition τ τ' σ B) :
    mixedTimeOrderedAtomicLegEquiv τ τ' υ
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p).1 =
      mixedTimeOrderedAtomicLegEquiv τ τ' σ p.1 := by
  rw [← twoPointLegEquiv_mixedTimeAmbientPositionEquiv,
    ← twoPointLegEquiv_mixedTimeAmbientPositionEquiv]
  exact congrArg (Common.twoPointLegEquiv (Finset.univ : Finset (Fin n)))
    (d.mixedTimeAmbientPositionEquiv_positionTimeEquiv τ τ' σ υ B p)

/-- Under component-local equality of interaction times, the supporting event of every mixed
component position has the same time at both assignments. -/
theorem FixedExternalTwoPointWickDiagram.componentPosition_eventTime_eq
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.1.componentPartition.parts)
    (hTime : d.ComponentTimeEq B σ υ)
    (p : d.MixedComponentPosition τ τ' σ B) :
    twoPointTimedEventTime τ τ' σ
        (orderedTwoPointLegEvent
          (mixedTimeOrderedAtomicLegEquiv τ τ' σ p.1)) =
      twoPointTimedEventTime τ τ' υ
        (orderedTwoPointLegEvent
          (mixedTimeOrderedAtomicLegEquiv τ τ' σ p.1)) := by
  have hAmbient :
      d.1.legInComponent
        (B : Finset (Common.TwoPointVertex
          (Finset.univ : Finset (Fin n))))
        (mixedTimeAmbientPositionEquiv τ τ' σ p.1) :=
    (d.mixedPositionComponent_eq_iff_legInComponent τ τ' σ B p.1).1 p.2
  have hUnflattened :=
    (d.1.legInComponent_iff_unflattened B
      (mixedTimeAmbientPositionEquiv τ τ' σ p.1)).1 hAmbient
  rw [twoPointLegEquiv_mixedTimeAmbientPositionEquiv] at hUnflattened
  generalize hleg : mixedTimeOrderedAtomicLegEquiv τ τ' σ p.1 = leg at hUnflattened ⊢
  cases leg with
  | inl e =>
      simp [orderedTwoPointLegEvent, twoPointTimedEventTime]
  | inr leg =>
      have hvB :
          (Sum.inr leg.1 : Common.TwoPointVertex
            (Finset.univ : Finset (Fin n))) ∈
            (B : Finset (Common.TwoPointVertex
              (Finset.univ : Finset (Fin n)))) := by
        simpa [Common.TwoPointDiagram.unflattenedLegInComponent,
          Common.twoPointLegVertex] using hUnflattened
      have hvPart :
          (leg.1.1 : Fin n) ∈ Common.TwoPointDiagram.interactionPart
            (B : Finset (Common.TwoPointVertex
              (Finset.univ : Finset (Fin n)))) :=
        (Common.TwoPointDiagram.mem_interactionPart_subtype
          (B : Finset (Common.TwoPointVertex
            (Finset.univ : Finset (Fin n)))) leg.1).2 hvB
      simpa [orderedTwoPointLegEvent, twoPointTimedEventTime] using
        hTime leg.1.1 hvPart

/-- Component position transport preserves strict mixed order as soon as the flattened atomic-leg
order of the two supporting legs is preserved.  This is the coordinate bookkeeping shared by every
sufficient condition for order preservation. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentPositionTimeEquiv_lt_iff_of_legPosition_lt_iff
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.1.componentPartition.parts)
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
theorem FixedExternalTwoPointWickDiagram.mixedComponentPositionTimeEquiv_lt_iff
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.1.componentPartition.parts)
    (hTime : d.ComponentTimeEq B σ υ)
    (p q : d.MixedComponentPosition τ τ' σ B) :
    p.1 < q.1 ↔
      (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p).1 <
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B q).1 :=
  d.mixedComponentPositionTimeEquiv_lt_iff_of_legPosition_lt_iff τ τ' σ υ B p q
    (mixedTimeOrderedAtomicLegPosition_lt_iff_of_eventTime_eq τ τ' σ υ _ _
      (d.componentPosition_eventTime_eq τ τ' σ υ B hTime p)
      (d.componentPosition_eventTime_eq τ τ' σ υ B hTime q))

/-- External-component restricted position coordinates are unchanged by time transport. -/
@[simp]
theorem FixedExternalTwoPointWickDiagram.mixedExternalPositionEquiv_positionTimeEquiv
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ υ : Fin n → ℝ)
    (p : d.MixedComponentPosition τ τ' σ d.1.externalComponentPart) :
    d.mixedExternalPositionEquiv τ τ' υ
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ d.1.externalComponentPart p) =
      d.mixedExternalPositionEquiv τ τ' σ p := by
  simp [FixedExternalTwoPointWickDiagram.mixedExternalPositionEquiv,
    FixedExternalTwoPointWickDiagram.mixedComponentPositionTimeEquiv]

/-- Vacuum-component restricted position coordinates are unchanged by time transport. -/
@[simp]
theorem FixedExternalTwoPointWickDiagram.mixedVacuumPositionEquiv_positionTimeEquiv
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.1.componentPartition.parts)
    (hVac : d.1.ComponentIsVacuum B)
    (p : d.MixedComponentPosition τ τ' σ B) :
    d.mixedVacuumPositionEquiv τ τ' υ B hVac
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p) =
      d.mixedVacuumPositionEquiv τ τ' σ B hVac p := by
  simp [FixedExternalTwoPointWickDiagram.mixedVacuumPositionEquiv,
    FixedExternalTwoPointWickDiagram.mixedComponentPositionTimeEquiv]

end Fermionic
end SecondQuantization
