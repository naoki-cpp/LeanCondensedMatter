import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.InteractionVertexRelabelTime

set_option linter.style.header false

/-!
# Mixed atomic positions under interaction-vertex relabeling

For a relabeled fixed diagram, a new interaction slot `v` inherits the old slot `π v`.  At a fixed
new time assignment `σ`, the corresponding old time assignment is therefore
`fun v => σ (π.symm v)`.

This file records the induced permutation from the new mixed-time atomic positions to the old
mixed-time atomic positions.  It is defined by converting a new mixed position to its standard leg,
relabeling that standard leg by `π`, and then locating the resulting old leg in the old mixed order.
The physical event time is preserved exactly.  Consequently, whenever two supporting event times
are distinct, the induced position permutation preserves their relative order.  Any possible order
change is therefore confined to equal-time event blocks.
-/

namespace SecondQuantization
namespace Fermionic

/-- The permutation from mixed atomic positions of the relabeled diagram at time assignment `σ` to
mixed atomic positions of the old diagram at the corresponding assignment
`fun v => σ (π.symm v)`.

The permutation maps a new mixed position to the old mixed position occupied by the standard leg
whose interaction slot is inherited under `π`. -/
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
  simp [mixedTimeOrderedAtomicLegPosition]

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

/-- For two positions supported on events at distinct physical times, interaction-vertex relabeling
preserves their mixed-order comparison.  Hence every possible order change is confined to equal-time
event blocks. -/
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
    simp [x, y, mixedTimeOrderedAtomicLegPosition]
  · simpa [x, y] using hTime

/-- With injective interaction times, transported mixed positions preserve order whenever their
supporting events are distinct.  Equal external/interaction times are allowed: their stable rank is
unchanged by interaction-slot relabeling. -/
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
  simp [x, y, mixedTimeOrderedAtomicLegPosition]

end Fermionic
end SecondQuantization
