import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedPositionLeg
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedVacuumEventBlocks

set_option linter.style.header false

/-!
# Mixed ordering of vacuum-component interaction blocks

This module connects the abstract four-leg vacuum blocks to the concrete atomic-leg blocks in the
mixed-time flattened list.  Each quartic local leg is represented by its standard two-point leg
identity, and the corresponding mixed position is proved to lie in the component containing that
interaction vertex.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*}

/-- Standard two-point leg identity of one local leg of an interaction slot. -/
def mixedTimeOrderedInteractionLeg {n : ℕ} (v : Fin n) (l : Fin 4) :
    OrderedTwoPointLeg n :=
  Sum.inr (⟨v, Finset.mem_univ v⟩, l)

/-- One local interaction leg belongs to its four-leg event block. -/
theorem mixedTimeOrderedInteractionLeg_mem_eventBlock {n : ℕ}
    (v : Fin n) (l : Fin 4) :
    mixedTimeOrderedInteractionLeg v l ∈
      twoPointTimedEventAtomicLegs (Sum.inr v : TwoPointTimedEvent n) := by
  fin_cases l <;>
    simp [mixedTimeOrderedInteractionLeg, twoPointTimedEventAtomicLegs]

/-- Every interaction event occurs in the actual mixed-time event order. -/
theorem interactionEvent_mem_orderedTwoPointTimedEvents {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) (v : Fin n) :
    (Sum.inr v : TwoPointTimedEvent n) ∈ orderedTwoPointTimedEvents τ τ' σ := by
  exact (orderedTwoPointTimedEvents_perm τ τ' σ).symm.subset (by
    simp [twoPointInteractionEventList])

/-- The mixed position selected by a local interaction leg belongs to the component containing that
interaction vertex. -/
theorem FixedExternalTwoPointWickDiagram.mixedPositionComponent_interactionLegPosition
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (C : d.1.componentPartition.parts)
    (v : ↥(Common.TwoPointDiagram.interactionPart
      (C : Finset (Common.TwoPointVertex
        (Finset.univ : Finset (Fin n)))))) (l : Fin 4) :
    d.mixedPositionComponent τ τ' σ
        (mixedTimeOrderedAtomicLegPosition τ τ' σ
          (mixedTimeOrderedInteractionLeg v.1 l)) = C := by
  rw [d.mixedPositionComponent_eq_iff_legInComponent,
    d.1.legInComponent_iff_unflattened,
    twoPointLegEquiv_mixedTimeAmbientPositionEquiv,
    mixedTimeOrderedAtomicLegEquiv_mixedTimeOrderedAtomicLegPosition]
  change (Sum.inr ⟨v.1, Finset.mem_univ v.1⟩ :
      Common.TwoPointVertex (Finset.univ : Finset (Fin n))) ∈
    (C : Finset (Common.TwoPointVertex
      (Finset.univ : Finset (Fin n))))
  exact (Common.TwoPointDiagram.mem_interactionPart_subtype
    (C : Finset (Common.TwoPointVertex
      (Finset.univ : Finset (Fin n))))
    ⟨v.1, Finset.mem_univ v.1⟩).1 v.2

/-- The mixed component position represented directly by one vacuum interaction leg. -/
noncomputable def FixedExternalTwoPointWickDiagram.directMixedVacuumInteractionPosition
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (C : d.1.componentPartition.parts)
    (v : ↥(Common.TwoPointDiagram.interactionPart
      (C : Finset (Common.TwoPointVertex
        (Finset.univ : Finset (Fin n)))))) (l : Fin 4) :
    d.MixedComponentPosition τ τ' σ C :=
  ⟨mixedTimeOrderedAtomicLegPosition τ τ' σ
      (mixedTimeOrderedInteractionLeg v.1 l),
    d.mixedPositionComponent_interactionLegPosition τ τ' σ C v l⟩

/-- The existing vacuum-position data equivalence sends the concrete mixed interaction position to
its vertex and local-leg coordinates. -/
theorem FixedExternalTwoPointWickDiagram.mixedVacuumPositionDataEquiv_direct
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (C : d.1.componentPartition.parts) (hVac : d.1.ComponentIsVacuum C)
    (v : ↥(Common.TwoPointDiagram.interactionPart
      (C : Finset (Common.TwoPointVertex
        (Finset.univ : Finset (Fin n)))))) (l : Fin 4) :
    d.mixedVacuumPositionDataEquiv τ τ' σ C hVac
        (d.directMixedVacuumInteractionPosition τ τ' σ C v l) = (v, l) := by
  simp only [FixedExternalTwoPointWickDiagram.mixedVacuumPositionDataEquiv,
    FixedExternalTwoPointWickDiagram.mixedVacuumPositionEquiv,
    FixedExternalTwoPointWickDiagram.mixedComponentPositionEquiv,
    Common.TwoPointDiagram.vacuumBlockLegEquiv, Equiv.trans_apply,
    Equiv.apply_symm_apply]
  let leg :
      {leg : OrderedTwoPointLeg n // d.1.unflattenedLegInComponent C leg} :=
    ((Common.twoPointLegEquiv (Finset.univ : Finset (Fin n))).subtypeEquiv
      (fun q => d.1.legInComponent_iff_unflattened C q))
      (((mixedTimeAmbientPositionEquiv τ τ' σ).subtypeEquiv
        (fun q => d.mixedPositionComponent_eq_iff_legInComponent τ τ' σ C q))
        (d.directMixedVacuumInteractionPosition τ τ' σ C v l))
  have hlegVal : leg.1 = mixedTimeOrderedInteractionLeg v.1 l := by
    change Common.twoPointLegEquiv (Finset.univ : Finset (Fin n))
        (mixedTimeAmbientPositionEquiv τ τ' σ
          (mixedTimeOrderedAtomicLegPosition τ τ' σ
            (mixedTimeOrderedInteractionLeg v.1 l))) =
      mixedTimeOrderedInteractionLeg v.1 l
    rw [twoPointLegEquiv_mixedTimeAmbientPositionEquiv,
      mixedTimeOrderedAtomicLegEquiv_mixedTimeOrderedAtomicLegPosition]
  have htarget : d.1.unflattenedLegInComponent C
      (mixedTimeOrderedInteractionLeg v.1 l) := by
    change (Sum.inr ⟨v.1, Finset.mem_univ v.1⟩ :
        Common.TwoPointVertex (Finset.univ : Finset (Fin n))) ∈
      (C : Finset (Common.TwoPointVertex
        (Finset.univ : Finset (Fin n))))
    exact (Common.TwoPointDiagram.mem_interactionPart_subtype
      (C : Finset (Common.TwoPointVertex
        (Finset.univ : Finset (Fin n))))
      ⟨v.1, Finset.mem_univ v.1⟩).1 v.2
  have hleg : leg = ⟨mixedTimeOrderedInteractionLeg v.1 l, htarget⟩ :=
    Subtype.ext hlegVal
  change d.1.vacuumLegDataEquiv C hVac leg = (v, l)
  rw [hleg]
  apply Prod.ext
  · apply Subtype.ext
    rfl
  · rfl

/-- The abstract inverse of the vacuum-position equivalence is the concrete mixed atomic position of
the corresponding interaction leg. -/
theorem FixedExternalTwoPointWickDiagram.mixedVacuumInteractionPosition_eq_direct
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (C : d.1.componentPartition.parts) (hVac : d.1.ComponentIsVacuum C)
    (v : ↥(Common.TwoPointDiagram.interactionPart
      (C : Finset (Common.TwoPointVertex
        (Finset.univ : Finset (Fin n)))))) (l : Fin 4) :
    d.mixedVacuumInteractionPosition τ τ' σ C hVac v l =
      d.directMixedVacuumInteractionPosition τ τ' σ C v l := by
  apply (d.mixedVacuumPositionDataEquiv τ τ' σ C hVac).injective
  unfold FixedExternalTwoPointWickDiagram.mixedVacuumInteractionPosition
  rw [Equiv.apply_symm_apply,
    d.mixedVacuumPositionDataEquiv_direct τ τ' σ C hVac v l]

@[simp]
theorem FixedExternalTwoPointWickDiagram.mixedVacuumInteractionPosition_val
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (C : d.1.componentPartition.parts) (hVac : d.1.ComponentIsVacuum C)
    (v : ↥(Common.TwoPointDiagram.interactionPart
      (C : Finset (Common.TwoPointVertex
        (Finset.univ : Finset (Fin n)))))) (l : Fin 4) :
    (d.mixedVacuumInteractionPosition τ τ' σ C hVac v l).1 =
      mixedTimeOrderedAtomicLegPosition τ τ' σ
        (mixedTimeOrderedInteractionLeg v.1 l) := by
  rw [d.mixedVacuumInteractionPosition_eq_direct]
  rfl

end Fermionic
end SecondQuantization
