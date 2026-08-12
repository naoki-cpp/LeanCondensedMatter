import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.DysonSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedExternalPositions
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.ComponentAmplitudeFactorization
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplitConnectivity

set_option linter.style.header false

/-!
# The connected perturbative two-point series

Summing only the externally connected diagrams at each order gives the connected two-point series.
The linked-cluster theorem says that this series is the vacuum-normalized one — the vacuum factors
that `ComponentAmplitudeFactorization` splits off are exactly what the division by the partition
series removes.

Connectedness is the ambient `TwoPointDiagram.IsExternallyConnected`. What this module adds is the
**slot characterization**: a diagram is externally connected exactly when its external component owns
every interaction slot. That is the form `externalFiberEquiv` indexes the fiber decomposition by, so
it is what identifies the connected diagrams with the `T = univ` fiber.

This module owns the connected series itself; the theorem identifying it is separate.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {n : ℕ} {i j : Mode}

omit [LinearOrder Mode] [Fintype Mode] in
/-- The slots the external component owns are the interaction part of the external component: the
index the fiberwise diagram sum is organized by. -/
theorem FixedExternalTwoPointWickDiagram.externalSlots_eq_interactionPart
    (d : FixedExternalTwoPointWickDiagram Mode n i j) :
    d.externalSlots =
      Common.TwoPointDiagram.interactionPart (d.1.externalComponent 0) := rfl

omit [LinearOrder Mode] [Fintype Mode] in
/-- **Externally connected means owning every slot.** A slot the external component does not own
belongs to a component containing no external vertex; conversely, a component that contains an
external vertex is the external one, so if none is vacuum every slot is external.

This is the `T = univ` case of the index of `TwoPointDiagram.externalFiberEquiv`. -/
theorem FixedExternalTwoPointWickDiagram.isExternallyConnected_iff_externalSlots_eq_univ
    (d : FixedExternalTwoPointWickDiagram Mode n i j) :
    d.1.IsExternallyConnected ↔ d.externalSlots = (Finset.univ : Finset (Fin n)) := by
  rw [Common.TwoPointDiagram.isExternallyConnected_iff_hasNoVacuumComponent,
    Common.TwoPointDiagram.hasNoVacuumComponent_iff_forall_component_meetsExternal]
  constructor
  · intro hall
    apply Finset.eq_univ_of_forall
    intro w
    rw [FixedExternalTwoPointWickDiagram.externalSlots_eq_interactionPart,
      Common.TwoPointDiagram.mem_interactionPart]
    refine ⟨Finset.mem_univ w, ?_⟩
    obtain ⟨e, he⟩ := hall ⟨d.1.componentBlock (Sum.inr ⟨w, Finset.mem_univ w⟩),
      d.1.componentBlock_mem_componentPartition _⟩
    have hblock : d.1.externalComponent e =
        d.1.componentBlock (Sum.inr ⟨w, Finset.mem_univ w⟩) :=
      (d.1.componentBlock_eq_iff_mem
        (d.1.componentBlock_mem_componentPartition _) (Sum.inl e)).2 he
    have hzero : d.1.externalComponent e = d.1.externalComponent 0 := by
      fin_cases e
      · rfl
      · exact d.1.externalComponent_zero_eq_one.symm
    rw [← hzero, hblock]
    exact d.1.self_mem_componentBlock _
  · intro hconn B
    obtain ⟨v, hv⟩ := d.1.exists_componentBlock_eq_of_mem B.2
    cases v with
    | inl e => exact ⟨e, hv ▸ d.1.self_mem_componentBlock (Sum.inl e)⟩
    | inr w =>
        have hmem : (w : Fin n) ∈ d.externalSlots := by
          rw [hconn]
          exact Finset.mem_univ _
        rw [FixedExternalTwoPointWickDiagram.externalSlots_eq_interactionPart,
          Common.TwoPointDiagram.mem_interactionPart] at hmem
        obtain ⟨hw, hw'⟩ := hmem
        have hvertex : (Sum.inr w :
            Common.TwoPointVertex (Finset.univ : Finset (Fin n))) ∈
            d.1.externalComponent 0 := by simpa using hw'
        have hB : (B : Finset (Common.TwoPointVertex (Finset.univ : Finset (Fin n)))) =
            d.1.externalComponent 0 := by
          rw [← hv]
          exact (d.1.componentBlock_eq_iff_mem
            (d.1.externalComponent_mem_componentPartition 0) (Sum.inr w)).2 hvertex
        refine ⟨0, ?_⟩
        rw [hB]
        exact d.1.self_mem_componentBlock (Sum.inl 0)

omit [LinearOrder Mode] [Fintype Mode] in
/-- A connected diagram's external component owns all `n` interaction slots. -/
theorem FixedExternalTwoPointWickDiagram.interactionComponentSize_externalComponentPart_of_connected
    (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (hconn : d.1.IsExternallyConnected) :
    d.1.interactionComponentSize d.1.externalComponentPart = n := by
  have hsize : d.1.interactionComponentSize d.1.externalComponentPart =
      d.externalSlots.card := rfl
  rw [hsize, d.isExternallyConnected_iff_externalSlots_eq_univ.1 hconn, Finset.card_univ,
    Fintype.card_fin]

/-- **On a connected diagram the shuffle-orbit sum is a single ordered-simplex integral.** There is
no vacuum factor left: the external component owns everything. -/
theorem FixedExternalTwoPointWickDiagram.sum_componentInteractionShuffle_dysonAmplitude_of_connected
    (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β) (g : QuarticVertexLabel Mode → ℂ) (τ τ' : ℝ)
    (hconn : d.1.IsExternallyConnected) :
    (∑ shuffle : d.1.ComponentInteractionShuffle,
        (d.relabelForComponentShuffle shuffle).dysonAmplitude ε β g τ τ') =
      twoPointExternalOrderSign τ τ' *
        intervalIntegral.orderedSimplexIntegral
          (d.1.interactionComponentSize d.1.externalComponentPart) β
          (d.mixedComponentDysonLocalIntegrand ε β g τ τ'
            d.1.canonicalComponentInteractionShuffle d.1.externalComponentPart) := by
  rw [d.sum_componentInteractionShuffle_dysonAmplitude_relabelForComponentShuffle_eq_external_mul_prod_vacuum
      ε β hβ g τ τ',
    (Common.TwoPointDiagram.isExternallyConnected_iff_vacuumComponentParts_eq_empty d.1).1 hconn,
    Finset.prod_empty, mul_one]

open Classical in
/-- The order-`n` coefficient of the connected two-point series: the integrated Dyson amplitudes of
the externally connected diagrams only. -/
noncomputable def connectedTwoPointDysonCoefficient (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) (n : ℕ) : ℂ :=
  ∑ d ∈ (Finset.univ : Finset (FixedExternalTwoPointWickDiagram Mode n i j)).filter
      fun d => d.1.IsExternallyConnected,
    d.dysonAmplitude ε β g τ τ'

/-- **The connected perturbative two-point series.** -/
noncomputable def connectedTwoPointDysonSeries (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) : PowerSeries ℂ :=
  PowerSeries.mk (connectedTwoPointDysonCoefficient ε β g i j τ τ')

@[simp]
theorem coeff_connectedTwoPointDysonSeries (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) (n : ℕ) :
    PowerSeries.coeff n (connectedTwoPointDysonSeries ε β g i j τ τ') =
      connectedTwoPointDysonCoefficient ε β g i j τ τ' n :=
  PowerSeries.coeff_mk n _

omit [LinearOrder Mode] [Fintype Mode] in
/-- At order zero there are no interaction slots, so every diagram is connected. -/
theorem isExternallyConnected_of_zero (d : FixedExternalTwoPointWickDiagram Mode 0 i j) :
    d.1.IsExternallyConnected := by
  rw [d.isExternallyConnected_iff_externalSlots_eq_univ]
  apply Finset.eq_univ_of_forall
  intro x
  exact x.elim0

open Classical in
/-- Hence the order-zero connected coefficient is the whole order-zero diagram sum: the free
two-point function has no vacuum part to remove. -/
theorem connectedTwoPointDysonCoefficient_zero (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) :
    connectedTwoPointDysonCoefficient ε β g i j τ τ' 0 =
      ∑ d : FixedExternalTwoPointWickDiagram Mode 0 i j, d.dysonAmplitude ε β g τ τ' := by
  rw [connectedTwoPointDysonCoefficient,
    Finset.filter_true_of_mem fun d _ => isExternallyConnected_of_zero d]

end Fermionic
end SecondQuantization
