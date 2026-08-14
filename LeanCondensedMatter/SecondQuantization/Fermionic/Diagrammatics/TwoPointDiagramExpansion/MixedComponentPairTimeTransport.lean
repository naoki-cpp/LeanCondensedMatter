import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentPairingValue

set_option linter.style.header false

/-!
# Transporting mixed component pairs across interaction-time assignments

The normalized pairs belonging to one full component are indexed by the mixed-time ordering and
therefore form different dependent types for two interaction-time assignments.  This module compares
those types through the fixed restricted external or vacuum pairing.

The resulting canonical equivalence isolates the two facts needed for component locality:

- preservation of the component-internal crossing relation;
- preservation of each finite Gibbs pair contraction.

Once these hold, the component crossing weight, contraction product, and complete mixed component
pairing value are equal at the two time assignments.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*}

/-- Canonical comparison of the mixed normalized pairs of one full component at two interaction-time
assignments.  The comparison passes through the time-independent restricted external or vacuum
pairing. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedComponentPairTimeEquiv
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.1.componentPartition.parts) :
    d.MixedComponentPair τ τ' σ B ≃ d.MixedComponentPair τ τ' υ B := by
  classical
  by_cases hB : B = d.1.externalComponentPart
  · subst B
    exact (d.mixedExternalComponentPairEquiv τ τ' σ).trans
      (d.mixedExternalComponentPairEquiv τ τ' υ).symm
  · have hVac : d.1.ComponentIsVacuum B :=
      (d.1.componentIsVacuum_iff_ne_externalComponentPart B).2 hB
    exact (d.mixedVacuumComponentPairEquiv τ τ' σ B hVac).trans
      (d.mixedVacuumComponentPairEquiv τ τ' υ B hVac).symm

@[simp]
theorem FixedExternalTwoPointWickDiagram.mixedComponentPairTimeEquiv_refl
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.1.componentPartition.parts)
    (pr : d.MixedComponentPair τ τ' σ B) :
    d.mixedComponentPairTimeEquiv τ τ' σ σ B pr = pr := by
  classical
  by_cases hB : B = d.1.externalComponentPart
  · subst B
    simp [FixedExternalTwoPointWickDiagram.mixedComponentPairTimeEquiv]
  · simp [FixedExternalTwoPointWickDiagram.mixedComponentPairTimeEquiv, hB]

/-- The canonical pair transport preserves the component-internal crossing predicate. -/
def FixedExternalTwoPointWickDiagram.MixedComponentCrossingPreserving
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.1.componentPartition.parts) : Prop :=
  ∀ p q : d.MixedComponentPair τ τ' σ B,
    Crosses p.1.1 q.1.1 ↔
      Crosses
        (d.mixedComponentPairTimeEquiv τ τ' σ υ B p).1.1
        (d.mixedComponentPairTimeEquiv τ τ' σ υ B q).1.1

/-- Crossing preservation under the canonical time transport gives equality of the component-
internal crossing counts. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentCrossingCount_eq_of_timeTransport
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.1.componentPartition.parts)
    (hCross : d.MixedComponentCrossingPreserving τ τ' σ υ B) :
    d.mixedComponentCrossingCount τ τ' σ B =
      d.mixedComponentCrossingCount τ τ' υ B := by
  classical
  let e := d.mixedComponentPairTimeEquiv τ τ' σ υ B
  let ee := Equiv.prodCongr e e
  unfold FixedExternalTwoPointWickDiagram.mixedComponentCrossingCount
    FixedExternalTwoPointWickDiagram.mixedComponentOrientedCrossingCount
  calc
    (∑ x : d.MixedComponentPair τ τ' σ B × d.MixedComponentPair τ τ' σ B,
        if Crosses x.1.1.1 x.2.1.1 then 1 else 0) =
      ∑ x : d.MixedComponentPair τ τ' σ B × d.MixedComponentPair τ τ' σ B,
        if Crosses (e x.1).1.1 (e x.2).1.1 then 1 else 0 := by
      apply Fintype.sum_congr
      intro x
      exact if_congr (hCross x.1 x.2) rfl rfl
    _ = ∑ y : d.MixedComponentPair τ τ' υ B × d.MixedComponentPair τ τ' υ B,
        if Crosses y.1.1.1 y.2.1.1 then 1 else 0 := by
      exact Equiv.sum_comp ee
        (fun y : d.MixedComponentPair τ τ' υ B × d.MixedComponentPair τ τ' υ B =>
          if Crosses y.1.1.1 y.2.1.1 then 1 else 0)

/-- Crossing preservation gives equality of the exchange-statistics weight of one component. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentWeight_eq_of_timeTransport
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (s : Common.Statistics) (τ τ' : ℝ) (σ υ : Fin n → ℝ)
    (B : d.1.componentPartition.parts)
    (hCross : d.MixedComponentCrossingPreserving τ τ' σ υ B) :
    d.mixedComponentWeight s τ τ' σ B =
      d.mixedComponentWeight s τ τ' υ B := by
  unfold FixedExternalTwoPointWickDiagram.mixedComponentWeight
  rw [d.mixedComponentCrossingCount_eq_of_timeTransport τ τ' σ υ B hCross]

section GibbsContractions

variable [LinearOrder Mode] [Fintype Mode]

/-- The canonical pair transport preserves the finite Gibbs contraction attached to every pair. -/
def FixedExternalTwoPointWickDiagram.MixedComponentContractionPreserving
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ) (σ υ : Fin n → ℝ)
    (B : d.1.componentPartition.parts) : Prop :=
  ∀ p : d.MixedComponentPair τ τ' σ B,
    d.mixedPairContractionValue ε β τ τ' σ p.1 =
      d.mixedPairContractionValue ε β τ τ' υ
        (d.mixedComponentPairTimeEquiv τ τ' σ υ B p).1

/-- Product of finite Gibbs contractions internal to one full component. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedComponentContractionProduct
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B : d.1.componentPartition.parts) : ℂ :=
  ∏ pr : d.MixedComponentPair τ τ' σ B,
    d.mixedPairContractionValue ε β τ τ' σ pr.1

/-- Contraction preservation under the canonical time transport gives equality of the complete
component pair-contraction products. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentContractionProduct_eq_of_timeTransport
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ) (σ υ : Fin n → ℝ)
    (B : d.1.componentPartition.parts)
    (hContraction : d.MixedComponentContractionPreserving ε β τ τ' σ υ B) :
    d.mixedComponentContractionProduct ε β τ τ' σ B =
      d.mixedComponentContractionProduct ε β τ τ' υ B := by
  classical
  let e := d.mixedComponentPairTimeEquiv τ τ' σ υ B
  unfold FixedExternalTwoPointWickDiagram.mixedComponentContractionProduct
  calc
    (∏ p : d.MixedComponentPair τ τ' σ B,
        d.mixedPairContractionValue ε β τ τ' σ p.1) =
      ∏ p : d.MixedComponentPair τ τ' σ B,
        d.mixedPairContractionValue ε β τ τ' υ (e p).1 := by
      apply Fintype.prod_congr
      intro p
      exact hContraction p
    _ = ∏ q : d.MixedComponentPair τ τ' υ B,
        d.mixedPairContractionValue ε β τ τ' υ q.1 := by
      exact Equiv.prod_comp e
        (fun q : d.MixedComponentPair τ τ' υ B =>
          d.mixedPairContractionValue ε β τ τ' υ q.1)

/-- The mixed component pairing value is its internal crossing weight times its component
contraction product. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentPairingValue_eq_weight_mul_contractionProduct
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B : d.1.componentPartition.parts) :
    d.mixedComponentPairingValue ε β τ τ' σ B =
      d.mixedComponentWeight Common.Statistics.fermion τ τ' σ B *
        d.mixedComponentContractionProduct ε β τ τ' σ B := by
  rfl

/-- Preservation of crossings and contractions under the canonical time transport gives equality of
the complete mixed component pairing values. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentPairingValue_eq_of_timeTransport
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ) (σ υ : Fin n → ℝ)
    (B : d.1.componentPartition.parts)
    (hCross : d.MixedComponentCrossingPreserving τ τ' σ υ B)
    (hContraction : d.MixedComponentContractionPreserving ε β τ τ' σ υ B) :
    d.mixedComponentPairingValue ε β τ τ' σ B =
      d.mixedComponentPairingValue ε β τ τ' υ B := by
  rw [d.mixedComponentPairingValue_eq_weight_mul_contractionProduct,
    d.mixedComponentPairingValue_eq_weight_mul_contractionProduct,
    d.mixedComponentWeight_eq_of_timeTransport Common.Statistics.fermion
      τ τ' σ υ B hCross,
    d.mixedComponentContractionProduct_eq_of_timeTransport
      ε β τ τ' σ υ B hContraction]

end GibbsContractions

end Fermionic
end SecondQuantization
