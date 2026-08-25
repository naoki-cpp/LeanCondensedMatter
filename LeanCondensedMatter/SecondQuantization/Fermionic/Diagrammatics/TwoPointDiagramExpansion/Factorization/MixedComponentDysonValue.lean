import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Factorization.MixedComponentFixedTimeValue

set_option linter.style.header false

/-!
# Component-local Dyson-signed values for two-point diagrams

The order-`n` Dyson sign depends only on the number of quartic interaction vertices. The interaction
vertices are partitioned by the full external-plus-interaction components, so this sign factors into
one power of `-1` for the canonical external component and one for every vacuum component.

This module combines those local signs with the component-local fixed-time values. The resulting
pointwise signed integrand is the exact input required by the subsequent ordered-simplex shuffle
factorization; no integration or continuity claim is made here. The external signed value is related
to the standalone external piece downstream in `ExternalPieceAmplitude`.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*}

/-- Dyson sign contributed by the interaction vertices in one full component. -/
@[implicit_reducible]
noncomputable def FixedExternalTwoPointWickDiagram.mixedComponentDysonSign
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (B : d.1.componentPartition.parts) : ℂ :=
  (-1 : ℂ) ^ (Common.TwoPointDiagram.interactionPart
    (B : Finset (Common.TwoPointVertex
      (Finset.univ : Finset (Fin n))))).card

private theorem FixedExternalTwoPointWickDiagram.dysonSign_eq_external_mul_prod_vacuum_mixed
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j) :
    (-1 : ℂ) ^ n = d.mixedComponentDysonSign d.1.externalComponentPart *
      d.1.vacuumComponentParts.prod d.mixedComponentDysonSign := by
  calc
    (-1 : ℂ) ^ n = (-1 : ℂ) ^ (Finset.univ : Finset (Fin n)).card := by simp
    _ = (-1 : ℂ) ^ (Common.TwoPointDiagram.interactionPart
          (d.1.externalComponent 0)).card *
        d.1.vacuumComponentParts.prod (fun B =>
          (-1 : ℂ) ^ (Common.TwoPointDiagram.interactionPart
            (B : Finset (Common.TwoPointVertex
              (Finset.univ : Finset (Fin n))))).card) :=
      d.1.dysonSign_eq_external_mul_prod_vacuum
    _ = d.mixedComponentDysonSign d.1.externalComponentPart *
        d.1.vacuumComponentParts.prod d.mixedComponentDysonSign := by
      have hext :
          (-1 : ℂ) ^ (Common.TwoPointDiagram.interactionPart
            (d.1.externalComponent 0)).card =
            d.mixedComponentDysonSign d.1.externalComponentPart := by
        rfl
      have hvac :
          d.1.vacuumComponentParts.prod (fun B =>
            (-1 : ℂ) ^ (Common.TwoPointDiagram.interactionPart
              (B : Finset (Common.TwoPointVertex
                (Finset.univ : Finset (Fin n))))).card) =
            d.1.vacuumComponentParts.prod d.mixedComponentDysonSign := by
        apply Finset.prod_congr rfl
        intro B hB
        rfl
      rw [hext, hvac]

section Fermionic

variable [LinearOrder Mode] [Fintype Mode]

/-- Dyson sign times the fixed-time value internal to one full component. -/
@[implicit_reducible]
noncomputable def FixedExternalTwoPointWickDiagram.mixedComponentDysonFixedTimeValue
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B : d.1.componentPartition.parts) : ℂ :=
  d.mixedComponentDysonSign B *
    d.mixedComponentFixedTimeValue ε β g τ τ' σ B

/-- The signed external value combines the external-component Dyson sign with the external ordering
sign and its component-local fixed-time value. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedExternalDysonFixedTimeValue
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ : Fin n → ℝ) : ℂ :=
  d.mixedComponentDysonSign d.1.externalComponentPart *
    d.mixedExternalFixedTimeValue ε β g τ τ' σ

/-- Pointwise fixed-time amplitude with the global order-`n` Dyson sign included. -/
noncomputable def FixedExternalTwoPointWickDiagram.dysonFixedTimeAmplitude
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ : Fin n → ℝ) : ℂ :=
  (-1 : ℂ) ^ n * d.fixedTimeAmplitude ε β g τ τ' σ

/-- The signed pointwise amplitude is the external ordering sign times the product of all signed
component-local fixed-time values. -/
theorem FixedExternalTwoPointWickDiagram.dysonFixedTimeAmplitude_eq_externalSign_mul_prod_components
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    d.dysonFixedTimeAmplitude ε β g τ τ' σ =
      twoPointExternalOrderSign τ τ' *
        ∏ B : d.1.componentPartition.parts,
          d.mixedComponentDysonFixedTimeValue ε β g τ τ' σ B := by
  unfold FixedExternalTwoPointWickDiagram.dysonFixedTimeAmplitude
  have hsign :
      (-1 : ℂ) ^ n = ∏ B : d.1.componentPartition.parts, d.mixedComponentDysonSign B := by
    calc
      (-1 : ℂ) ^ n = d.mixedComponentDysonSign d.1.externalComponentPart *
          d.1.vacuumComponentParts.prod d.mixedComponentDysonSign :=
        d.dysonSign_eq_external_mul_prod_vacuum_mixed
      _ = ∏ B : d.1.componentPartition.parts, d.mixedComponentDysonSign B := by
        rw [d.1.prod_componentParts_eq_external_mul_prod_vacuum]
  rw [hsign, d.fixedTimeAmplitude_eq_externalSign_mul_prod_components]
  unfold FixedExternalTwoPointWickDiagram.mixedComponentDysonFixedTimeValue
  rw [Finset.prod_mul_distrib]
  ring

/-- External/vacuum factorization of the signed pointwise fixed-time amplitude. -/
theorem FixedExternalTwoPointWickDiagram.dysonFixedTimeAmplitude_eq_external_mul_prod_vacuum
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    d.dysonFixedTimeAmplitude ε β g τ τ' σ =
      d.mixedExternalDysonFixedTimeValue ε β g τ τ' σ *
        d.1.vacuumComponentParts.prod
          (d.mixedComponentDysonFixedTimeValue ε β g τ τ' σ) := by
  unfold FixedExternalTwoPointWickDiagram.dysonFixedTimeAmplitude
  have hsign :
      (-1 : ℂ) ^ n = d.mixedComponentDysonSign d.1.externalComponentPart *
        d.1.vacuumComponentParts.prod d.mixedComponentDysonSign :=
    d.dysonSign_eq_external_mul_prod_vacuum_mixed
  rw [hsign, d.fixedTimeAmplitude_eq_externalSign_mul_prod_components,
    d.1.prod_componentParts_eq_external_mul_prod_vacuum]
  unfold FixedExternalTwoPointWickDiagram.mixedExternalDysonFixedTimeValue
  unfold FixedExternalTwoPointWickDiagram.mixedExternalFixedTimeValue
  unfold FixedExternalTwoPointWickDiagram.mixedComponentDysonFixedTimeValue
  rw [Finset.prod_mul_distrib]
  ring

end Fermionic

end Fermionic
end SecondQuantization
