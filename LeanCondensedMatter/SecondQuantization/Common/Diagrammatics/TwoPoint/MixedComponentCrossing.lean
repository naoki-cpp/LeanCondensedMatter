import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.MixedComponentPairProduct
import LeanCondensedMatter.Combinatorics.PerfectPairing.ComponentCrossing
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.PairingWeight

set_option linter.style.header false

/-!
# Crossing decomposition for mixed-time two-point pairings

This module reindexes the crossing count of a generic mixed-order two-point pairing by full connected
components. The construction and parity decomposition are statistics-independent; the final weight
formula is parameterized by `Statistics` rather than specialized to fermions.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

/-- Oriented crossing count from mixed normalized pairs in component `B` to pairs in component `C`. -/
noncomputable def TwoPointDiagram.mixedComponentOrientedCrossingCount
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B C : d.componentPartition.parts) : ℕ :=
  (d.pairingInMixedOrder τ τ' σ).componentCrossingCount
    (d.mixedComponentPairSigmaEquiv τ τ' σ) B C

/-- Crossing count internal to one mixed-time component. -/
noncomputable def TwoPointDiagram.mixedComponentCrossingCount
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.componentPartition.parts) : ℕ :=
  d.mixedComponentOrientedCrossingCount τ τ' σ B B

/-- Unoriented geometric crossing count between two mixed-time components. -/
noncomputable def TwoPointDiagram.mixedComponentGeometricCrossingCount
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B C : d.componentPartition.parts) : ℕ :=
  ∑ x : d.MixedComponentPair τ τ' σ B × d.MixedComponentPair τ τ' σ C,
    if Crosses x.1.1.1 x.2.1.1 ∨ Crosses x.2.1.1 x.1.1.1 then 1 else 0

/-- The geometric crossing count between two components is the sum of its two orientations. -/
theorem TwoPointDiagram.mixedComponentGeometricCrossingCount_eq_oriented_add
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B C : d.componentPartition.parts) :
    d.mixedComponentGeometricCrossingCount τ τ' σ B C =
      d.mixedComponentOrientedCrossingCount τ τ' σ B C +
        d.mixedComponentOrientedCrossingCount τ τ' σ C B := by
  simpa only [TwoPointDiagram.mixedComponentGeometricCrossingCount,
    Pairing.componentGeometricCrossingCount,
    TwoPointDiagram.mixedComponentOrientedCrossingCount] using
    (d.pairingInMixedOrder τ τ' σ).componentGeometricCrossingCount_eq_oriented_add
      (d.mixedComponentPairSigmaEquiv τ τ' σ) B C

private theorem TwoPointDiagram.pairingInMixedOrder_crossingCount_mod_two_eq_sum_components
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hEven : ∀ B C : d.componentPartition.parts, B ≠ C →
      d.mixedComponentGeometricCrossingCount τ τ' σ B C % 2 = 0) :
    (d.pairingInMixedOrder τ τ' σ).crossingCount % 2 =
      (∑ B : d.componentPartition.parts, d.mixedComponentCrossingCount τ τ' σ B) % 2 :=
  Combinatorics.Pairing.crossingCount_mod_two_eq_sum_componentCrossingCount
    (d.pairingInMixedOrder τ τ' σ) (d.mixedComponentPairSigmaEquiv τ τ' σ)
    (fun B C hBC => by
      change (d.mixedComponentOrientedCrossingCount τ τ' σ B C +
        d.mixedComponentOrientedCrossingCount τ τ' σ C B) % 2 = 0
      rw [← d.mixedComponentGeometricCrossingCount_eq_oriented_add τ τ' σ B C]
      exact hEven B C hBC)

/-- Exchange-statistics weight associated with crossings internal to one mixed-time component. -/
noncomputable def TwoPointDiagram.mixedComponentWeight
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (s : Statistics) (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.componentPartition.parts) : ℂ :=
  (s.zetaInt : ℂ) ^ d.mixedComponentCrossingCount τ τ' σ B

/-- Under even off-diagonal geometric crossing parity, the global mixed pairing weight is the
product of component-internal weights. -/
theorem TwoPointDiagram.pairingInMixedOrder_weight_eq_prod_components
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (s : Statistics) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hEven : ∀ B C : d.componentPartition.parts, B ≠ C →
      d.mixedComponentGeometricCrossingCount τ τ' σ B C % 2 = 0) :
    (d.pairingInMixedOrder τ τ' σ).weight s =
      ∏ B : d.componentPartition.parts, d.mixedComponentWeight s τ τ' σ B := by
  have hparity := d.pairingInMixedOrder_crossingCount_mod_two_eq_sum_components τ τ' σ hEven
  simpa only [Combinatorics.Pairing.weight, TwoPointDiagram.mixedComponentWeight] using
    BlochDeDominicis.zetaInt_pow_eq_prod_of_sum_mod_two_eq s
      (d.pairingInMixedOrder τ τ' σ).crossingCount
      (fun B : d.componentPartition.parts => d.mixedComponentCrossingCount τ τ' σ B) hparity

/-- Component weights split into the canonical external component and the vacuum components. -/
theorem TwoPointDiagram.prod_mixedComponentWeight_eq_external_mul_prod_vacuum
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (s : Statistics) (τ τ' : ℝ) (σ : Fin n → ℝ) :
    (∏ B : d.componentPartition.parts, d.mixedComponentWeight s τ τ' σ B) =
      d.mixedComponentWeight s τ τ' σ d.externalComponentPart *
        d.vacuumComponentParts.prod (d.mixedComponentWeight s τ τ' σ) :=
  d.prod_componentParts_eq_external_mul_prod_vacuum (d.mixedComponentWeight s τ τ' σ)

end Common
end SecondQuantization
