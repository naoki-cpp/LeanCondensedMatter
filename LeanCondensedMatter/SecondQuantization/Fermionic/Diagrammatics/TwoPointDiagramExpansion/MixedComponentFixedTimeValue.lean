import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentVertexProduct
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentPairingValue

set_option linter.style.header false

/-!
# Component-local fixed-time values for two-point diagrams

A fixed-time two-point Wick-diagram amplitude contains three scalar layers: the external-field time-
ordering sign, the product of quartic couplings, and the mixed-order pairing value.  The preceding
modules factor the pairing value over full external-plus-interaction components, while the common
two-point component API factors arbitrary interaction-vertex products.

This module combines those results.  It defines one coupling-and-pairing value for each full
component, packages the external ordering sign with the canonical external component, and proves that
the global fixed-time amplitude is the external value times the product of all vacuum-component
values. The external value is related to the standalone external piece downstream in
`ExternalPieceAmplitude`; restricted formulas here are retained only for vacuum components.

The Dyson sign and ordered-simplex integration are intentionally left to the next layer.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*}

private def univSubtypeEquiv (α : Type*) [Fintype α] :
    α ≃ ↥(Finset.univ : Finset α) where
  toFun x := ⟨x, Finset.mem_univ x⟩
  invFun x := x.1
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl

/-- Product of quartic couplings on the interaction vertices belonging to one full component. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedComponentVertexWeight
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (g : QuarticVertexLabel Mode → ℂ)
    (B : d.1.componentPartition.parts) : ℂ :=
  ∏ v : ↥(Common.TwoPointDiagram.interactionPart
      (B : Finset (Common.TwoPointVertex
        (Finset.univ : Finset (Fin n))))),
    g (d.1.vertexLabel
      ⟨v.1, Common.TwoPointDiagram.interactionPart_subset
        (B : Finset (Common.TwoPointVertex
          (Finset.univ : Finset (Fin n)))) v.2⟩)

/-- The slot-indexed quartic coupling product is the product of the component-local vertex
weights. -/
theorem FixedExternalTwoPointWickDiagram.orderedTwoPointVertexWeight_eq_prod_components
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (g : QuarticVertexLabel Mode → ℂ) :
    orderedTwoPointVertexWeight g d.vertexLabelSequence =
      ∏ B : d.1.componentPartition.parts,
        d.mixedComponentVertexWeight g B := by
  classical
  calc
    orderedTwoPointVertexWeight g d.vertexLabelSequence =
        ∏ v : ↥(Finset.univ : Finset (Fin n)), g (d.1.vertexLabel v) := by
      simpa [orderedTwoPointVertexWeight,
        FixedExternalTwoPointWickDiagram.vertexLabelSequence,
        univSubtypeEquiv] using
        (Equiv.prod_comp (univSubtypeEquiv (Fin n))
          (fun v : ↥(Finset.univ : Finset (Fin n)) => g (d.1.vertexLabel v)))
    _ = ∏ B : d.1.componentPartition.parts,
        ∏ v : ↥(Common.TwoPointDiagram.interactionPart
          (B : Finset (Common.TwoPointVertex
            (Finset.univ : Finset (Fin n))))),
          g (d.1.vertexLabel
            ⟨v.1, Common.TwoPointDiagram.interactionPart_subset
              (B : Finset (Common.TwoPointVertex
                (Finset.univ : Finset (Fin n)))) v.2⟩) :=
      d.1.prod_vertexLabel_eq_prod_componentInteractionParts g
    _ = ∏ B : d.1.componentPartition.parts,
        d.mixedComponentVertexWeight g B := rfl

/-- External/vacuum decomposition of the quartic coupling product. -/
theorem FixedExternalTwoPointWickDiagram.orderedTwoPointVertexWeight_eq_external_mul_prod_vacuum
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (g : QuarticVertexLabel Mode → ℂ) :
    orderedTwoPointVertexWeight g d.vertexLabelSequence =
      d.mixedComponentVertexWeight g d.1.externalComponentPart *
        d.1.vacuumComponentParts.prod (d.mixedComponentVertexWeight g) := by
  rw [d.orderedTwoPointVertexWeight_eq_prod_components g,
    d.1.prod_componentParts_eq_external_mul_prod_vacuum]

/-- A vacuum component vertex weight is the coupling product of its restricted vacuum diagram. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentVertexWeight_vacuum_eq_restricted
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (g : QuarticVertexLabel Mode → ℂ)
    (B : d.1.componentPartition.parts) (hVac : d.1.ComponentIsVacuum B) :
    d.mixedComponentVertexWeight g B =
      ∏ v : ↥(Common.TwoPointDiagram.interactionPart
        (B : Finset (Common.TwoPointVertex
          (Finset.univ : Finset (Fin n))))),
        g ((d.1.restrictVacuumComponent B hVac).vertexLabel v) := by
  rfl

section Fermionic

variable [LinearOrder Mode] [Fintype Mode]

/-- Coupling weight times mixed pairing value internal to one full component. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedComponentFixedTimeValue
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B : d.1.componentPartition.parts) : ℂ :=
  d.mixedComponentVertexWeight g B *
    d.mixedComponentPairingValue ε β τ τ' σ B

/-- The canonical external fixed-time value also carries the external-field ordering sign. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedExternalFixedTimeValue
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ : Fin n → ℝ) : ℂ :=
  twoPointExternalOrderSign τ τ' *
    d.mixedComponentFixedTimeValue ε β g τ τ' σ d.1.externalComponentPart

/-- The global fixed-time amplitude is the external ordering sign times the product of all
component-local fixed-time values. -/
theorem FixedExternalTwoPointWickDiagram.fixedTimeAmplitude_eq_externalSign_mul_prod_components
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    d.fixedTimeAmplitude ε β g τ τ' σ =
      twoPointExternalOrderSign τ τ' *
        ∏ B : d.1.componentPartition.parts,
          d.mixedComponentFixedTimeValue ε β g τ τ' σ B := by
  change twoPointExternalOrderSign τ τ' *
      orderedTwoPointVertexWeight g d.vertexLabelSequence *
        orderedTwoPointPairingValue ε β i j τ τ' σ d.vertexLabelSequence
          (d.pairingInMixedOrder τ τ' σ) = _
  rw [d.orderedTwoPointVertexWeight_eq_prod_components g,
    d.orderedTwoPointPairingValue_eq_prod_components_unconditional ε β τ τ' σ]
  unfold FixedExternalTwoPointWickDiagram.mixedComponentFixedTimeValue
  rw [Finset.prod_mul_distrib]
  ring

/-- External/vacuum factorization of the complete fixed-time amplitude. -/
theorem FixedExternalTwoPointWickDiagram.fixedTimeAmplitude_eq_external_mul_prod_vacuum
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    d.fixedTimeAmplitude ε β g τ τ' σ =
      d.mixedExternalFixedTimeValue ε β g τ τ' σ *
        d.1.vacuumComponentParts.prod
          (d.mixedComponentFixedTimeValue ε β g τ τ' σ) := by
  rw [d.fixedTimeAmplitude_eq_externalSign_mul_prod_components ε β g τ τ' σ,
    d.1.prod_componentParts_eq_external_mul_prod_vacuum]
  unfold FixedExternalTwoPointWickDiagram.mixedExternalFixedTimeValue
  ring

/-- Restricted-diagram expression for one vacuum-component fixed-time value. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentFixedTimeValue_vacuum_eq_restricted
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B : d.1.componentPartition.parts) (hVac : d.1.ComponentIsVacuum B) :
    d.mixedComponentFixedTimeValue ε β g τ τ' σ B =
      (∏ v : ↥(Common.TwoPointDiagram.interactionPart
        (B : Finset (Common.TwoPointVertex
          (Finset.univ : Finset (Fin n))))),
        g ((d.1.restrictVacuumComponent B hVac).vertexLabel v)) *
      d.mixedVacuumRestrictedPairingValue ε β τ τ' σ B hVac := by
  unfold FixedExternalTwoPointWickDiagram.mixedComponentFixedTimeValue
  rw [d.mixedComponentVertexWeight_vacuum_eq_restricted g B hVac,
    d.mixedComponentPairingValue_vacuum_eq_restricted ε β τ τ' σ B hVac]

end Fermionic

end Fermionic
end SecondQuantization
