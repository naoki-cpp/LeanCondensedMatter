import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedComponentPosition
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.MixedOrderChamber

set_option linter.style.header false

/-!
# Statistics-independent mixed component time transport

Mixed-time positions belonging to one full two-point diagram component can be compared across two
interaction-time assignments through their common standard component-leg fiber. This module owns the
resulting transport, its coordinate invariance, and preservation of mixed linear order inside one
global mixed-order chamber.

No contraction value, Gibbs expectation, exchange sign, or statistics specialization appears here.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*}

/-- Canonical comparison of mixed positions of one full component at two interaction-time
assignments. The comparison passes through the fixed standard component-leg fiber. -/
noncomputable def TwoPointDiagram.mixedComponentPositionTimeEquiv {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.componentPartition.parts) :
    d.MixedComponentPosition τ τ' σ B ≃ d.MixedComponentPosition τ τ' υ B :=
  (d.mixedComponentPositionEquiv τ τ' σ B).trans
    (d.mixedComponentPositionEquiv τ τ' υ B).symm

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

/-- Atomic-leg order is unchanged across assignments in the same mixed-event order chamber. -/
private theorem mixedTimeOrderedAtomicLegPosition_lt_iff_of_sameOrderChamber {n : ℕ}
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

end Common
end SecondQuantization
