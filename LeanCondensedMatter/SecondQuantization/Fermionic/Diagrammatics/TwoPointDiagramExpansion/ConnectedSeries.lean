import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.DysonSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedExternalPositions

set_option linter.style.header false

/-!
# The connected perturbative two-point series

A fixed-external two-point diagram is connected exactly when its external component owns every
interaction slot: any slot it does not own belongs to a vacuum component, and conversely a vacuum
component owns at least the slots of its own vertices.

Summing only the connected diagrams at each order gives the connected two-point series. The
linked-cluster theorem says that this series is the vacuum-normalized one — the vacuum factors that
`ComponentAmplitudeFactorization` splits off are exactly what the division by the partition series
removes.

This module owns the connected object itself; the theorem identifying it is separate.
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

/-- **A fixed-external diagram is connected** when its external component owns every interaction
slot, leaving no vacuum component to factor off. -/
def FixedExternalTwoPointWickDiagram.IsConnected
    (d : FixedExternalTwoPointWickDiagram Mode n i j) : Prop :=
  d.externalSlots = (Finset.univ : Finset (Fin n))

omit [LinearOrder Mode] [Fintype Mode] in
/-- **Owning every slot is the same as having no vacuum component.** A slot the external component
does not own belongs to a component containing no external vertex; conversely, a component that
contains an external vertex is the external one, so if none is vacuum every slot is external. -/
theorem FixedExternalTwoPointWickDiagram.isConnected_iff_hasNoVacuumComponent
    (d : FixedExternalTwoPointWickDiagram Mode n i j) :
    d.IsConnected ↔ d.1.HasNoVacuumComponent := by
  rw [Common.TwoPointDiagram.hasNoVacuumComponent_iff_forall_component_meetsExternal]
  constructor
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

open Classical in
/-- The order-`n` coefficient of the connected two-point series: the integrated Dyson amplitudes of
the connected diagrams only. -/
noncomputable def connectedTwoPointDysonCoefficient (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) (n : ℕ) : ℂ :=
  ∑ d ∈ (Finset.univ : Finset (FixedExternalTwoPointWickDiagram Mode n i j)).filter
      FixedExternalTwoPointWickDiagram.IsConnected,
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
theorem isConnected_of_zero (d : FixedExternalTwoPointWickDiagram Mode 0 i j) :
    d.IsConnected := by
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
    Finset.filter_true_of_mem fun d _ => isConnected_of_zero d]

end Fermionic
end SecondQuantization
