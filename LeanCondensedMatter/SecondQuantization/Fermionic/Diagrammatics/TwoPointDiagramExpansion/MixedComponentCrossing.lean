import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentPairProduct
import LeanCondensedMatter.Combinatorics.PerfectPairing.ComponentCrossing
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.PairingWeight

set_option linter.style.header false

/-!
# Crossing decomposition for mixed-time two-point pairings

The exchange-statistics weight in a two-point Wick amplitude is computed from the crossing count of
`pairingInMixedOrder`. This module reindexes that crossing count by full diagram components.
Diagonal component pairs give component-internal crossings, while off-diagonal component pairs give
the geometric crossings between two distinct components.

The crossing geometry remains local to the mixed-time two-point representation. Once its parity is
known, the finite-family exchange-weight algebra is delegated to the Common Statistics backend.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*}

/-- Oriented crossing count from mixed normalized pairs in component `B` to pairs in component `C`. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedComponentOrientedCrossingCount
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B C : d.1.componentPartition.parts) : ℕ :=
  (d.pairingInMixedOrder τ τ' σ).componentCrossingCount
    (d.mixedComponentPairSigmaEquiv τ τ' σ) B C

/-- Crossing count internal to one mixed-time component. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedComponentCrossingCount
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B : d.1.componentPartition.parts) : ℕ :=
  d.mixedComponentOrientedCrossingCount τ τ' σ B B

/-- Unoriented geometric crossing count between two mixed-time components. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedComponentGeometricCrossingCount
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B C : d.1.componentPartition.parts) : ℕ :=
  ∑ x : d.MixedComponentPair τ τ' σ B × d.MixedComponentPair τ τ' σ C,
    if Crosses x.1.1.1 x.2.1.1 ∨ Crosses x.2.1.1 x.1.1.1 then 1 else 0

/-- The geometric crossing count between two components is the sum of its two orientations. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentGeometricCrossingCount_eq_oriented_add
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B C : d.1.componentPartition.parts) :
    d.mixedComponentGeometricCrossingCount τ τ' σ B C =
      d.mixedComponentOrientedCrossingCount τ τ' σ B C +
        d.mixedComponentOrientedCrossingCount τ τ' σ C B := by
  classical
  have hswap : d.mixedComponentOrientedCrossingCount τ τ' σ C B =
      ∑ x : d.MixedComponentPair τ τ' σ B × d.MixedComponentPair τ τ' σ C,
        if Crosses x.2.1.1 x.1.1.1 then 1 else 0 := by
    rw [FixedExternalTwoPointWickDiagram.mixedComponentOrientedCrossingCount,
      Combinatorics.Pairing.componentCrossingCount,
      ← Equiv.sum_comp (Equiv.prodComm
        (d.MixedComponentPair τ τ' σ B) (d.MixedComponentPair τ τ' σ C))]
    rfl
  rw [FixedExternalTwoPointWickDiagram.mixedComponentGeometricCrossingCount, hswap,
    FixedExternalTwoPointWickDiagram.mixedComponentOrientedCrossingCount,
    Combinatorics.Pairing.componentCrossingCount,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hbc : Crosses x.1.1.1 x.2.1.1
  · have hcb : ¬ Crosses x.2.1.1 x.1.1.1 := fun h => lt_asymm hbc.1 h.1
    simp [hbc, hcb]
  · simp [hbc]

/-- If every distinct-component geometric crossing count is even, the global mixed crossing count
has the same parity as the sum of the component-internal crossing counts. -/
private theorem
    FixedExternalTwoPointWickDiagram.pairingInMixedOrder_crossingCount_mod_two_eq_sum_components
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hEven : ∀ B C : d.1.componentPartition.parts, B ≠ C →
      d.mixedComponentGeometricCrossingCount τ τ' σ B C % 2 = 0) :
    (d.pairingInMixedOrder τ τ' σ).crossingCount % 2 =
      (∑ B : d.1.componentPartition.parts,
        d.mixedComponentCrossingCount τ τ' σ B) % 2 :=
  Combinatorics.Pairing.crossingCount_mod_two_eq_sum_componentCrossingCount
    (d.pairingInMixedOrder τ τ' σ) (d.mixedComponentPairSigmaEquiv τ τ' σ)
    (fun B C hBC => by
      change (d.mixedComponentOrientedCrossingCount τ τ' σ B C +
        d.mixedComponentOrientedCrossingCount τ τ' σ C B) % 2 = 0
      rw [← d.mixedComponentGeometricCrossingCount_eq_oriented_add τ τ' σ B C]
      exact hEven B C hBC)

/-- Exchange-statistics weight associated with crossings internal to one mixed-time component. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedComponentWeight
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (s : Common.Statistics) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B : d.1.componentPartition.parts) : ℂ :=
  (s.zetaInt : ℂ) ^ d.mixedComponentCrossingCount τ τ' σ B

/-- Under even off-diagonal geometric crossing parity, the global mixed pairing weight is the
product of component-internal weights. -/
theorem FixedExternalTwoPointWickDiagram.pairingInMixedOrder_weight_eq_prod_components
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (s : Common.Statistics) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hEven : ∀ B C : d.1.componentPartition.parts, B ≠ C →
      d.mixedComponentGeometricCrossingCount τ τ' σ B C % 2 = 0) :
    (d.pairingInMixedOrder τ τ' σ).weight s =
      ∏ B : d.1.componentPartition.parts,
        d.mixedComponentWeight s τ τ' σ B := by
  have hparity :=
    d.pairingInMixedOrder_crossingCount_mod_two_eq_sum_components τ τ' σ hEven
  simpa only [Combinatorics.Pairing.weight,
    FixedExternalTwoPointWickDiagram.mixedComponentWeight] using
    Common.BlochDeDominicis.zetaInt_pow_eq_prod_of_sum_mod_two_eq s
      (d.pairingInMixedOrder τ τ' σ).crossingCount
      (fun B : d.1.componentPartition.parts => d.mixedComponentCrossingCount τ τ' σ B)
      hparity

/-- Component weights split into the canonical external component and the vacuum components. -/
theorem FixedExternalTwoPointWickDiagram.prod_mixedComponentWeight_eq_external_mul_prod_vacuum
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (s : Common.Statistics) (τ τ' : ℝ) (σ : Fin n → ℝ) :
    (∏ B : d.1.componentPartition.parts,
      d.mixedComponentWeight s τ τ' σ B) =
      d.mixedComponentWeight s τ τ' σ d.1.externalComponentPart *
        d.1.vacuumComponentParts.prod
          (d.mixedComponentWeight s τ τ' σ) :=
  d.1.prod_componentParts_eq_external_mul_prod_vacuum
    (d.mixedComponentWeight s τ τ' σ)

end Fermionic
end SecondQuantization
