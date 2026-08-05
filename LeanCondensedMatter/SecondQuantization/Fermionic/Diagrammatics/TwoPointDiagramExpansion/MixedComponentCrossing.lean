import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentPairProduct
import LeanCondensedMatter.Combinatorics.PerfectPairing.CrossingParity
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.PairingWeight

set_option linter.style.header false

/-!
# Crossing decomposition for mixed-time two-point pairings

The fermionic sign in a two-point Wick amplitude is computed from the crossing count of
`pairingInMixedOrder`.  This module reindexes that crossing count by full diagram components.
Diagonal component pairs give component-internal crossings, while off-diagonal component pairs give
the geometric crossings between two distinct components.

The final parity and weight factorization are stated assuming the off-diagonal geometric crossing
counts are even.  Proving that assumption from the one-leg external blocks and four-leg interaction
blocks is the next layer.
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
  ∑ x : d.MixedComponentPair τ τ' σ B × d.MixedComponentPair τ τ' σ C,
    if Crosses x.1.1.1 x.2.1.1 then 1 else 0

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

private theorem crosses_asymm {n : ℕ}
    (p q : Fin (2 * n) × Fin (2 * n)) (hpq : Crosses p q) :
    ¬ Crosses q p := by
  intro hqp
  exact lt_asymm hpq.1 hqp.1

private theorem indicator_or_eq_add_indicator_of_not_and
    (p q : Prop) [Decidable p] [Decidable q] (h : ¬ (p ∧ q)) :
    (if p ∨ q then 1 else 0 : ℕ) =
      (if p then 1 else 0) + (if q then 1 else 0) := by
  by_cases hp : p <;> by_cases hq : q <;> simp_all

/-- The geometric crossing count between two components is the sum of its two orientations. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentGeometricCrossingCount_eq_oriented_add
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B C : d.1.componentPartition.parts) :
    d.mixedComponentGeometricCrossingCount τ τ' σ B C =
      d.mixedComponentOrientedCrossingCount τ τ' σ B C +
        d.mixedComponentOrientedCrossingCount τ τ' σ C B := by
  classical
  let crossBC := fun x :
      d.MixedComponentPair τ τ' σ B × d.MixedComponentPair τ τ' σ C =>
    Crosses x.1.1.1 x.2.1.1
  let crossCB := fun x :
      d.MixedComponentPair τ τ' σ B × d.MixedComponentPair τ τ' σ C =>
    Crosses x.2.1.1 x.1.1.1
  have hswap :
      (∑ x : d.MixedComponentPair τ τ' σ C × d.MixedComponentPair τ τ' σ B,
        if Crosses x.1.1.1 x.2.1.1 then 1 else 0) =
        ∑ x : d.MixedComponentPair τ τ' σ B × d.MixedComponentPair τ τ' σ C,
          if crossCB x then 1 else 0 := by
    rw [← Equiv.sum_comp (Equiv.prodComm
      (d.MixedComponentPair τ τ' σ B) (d.MixedComponentPair τ τ' σ C))]
    rfl
  rw [FixedExternalTwoPointWickDiagram.mixedComponentGeometricCrossingCount,
    FixedExternalTwoPointWickDiagram.mixedComponentOrientedCrossingCount,
    FixedExternalTwoPointWickDiagram.mixedComponentOrientedCrossingCount, hswap]
  change (∑ x, if crossBC x ∨ crossCB x then 1 else 0) =
    (∑ x, if crossBC x then 1 else 0) + ∑ x, if crossCB x then 1 else 0
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  exact indicator_or_eq_add_indicator_of_not_and (crossBC x) (crossCB x) (by
    rintro ⟨hbc, hcb⟩
    exact crosses_asymm _ _ hbc hcb)

/-- The mixed pairing crossing count is the double sum of oriented crossing counts over full
components. -/
theorem FixedExternalTwoPointWickDiagram.pairingInMixedOrder_crossingCount_eq_sum_components
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    (d.pairingInMixedOrder τ τ' σ).crossingCount =
      ∑ B : d.1.componentPartition.parts,
        ∑ C : d.1.componentPartition.parts,
          d.mixedComponentOrientedCrossingCount τ τ' σ B C := by
  classical
  let globalPairing := d.pairingInMixedOrder τ τ' σ
  let pairEquiv := d.mixedComponentPairSigmaEquiv τ τ' σ
  let componentPairProductEquiv :
      (Σ BC : d.1.componentPartition.parts × d.1.componentPartition.parts,
        d.MixedComponentPair τ τ' σ BC.1 × d.MixedComponentPair τ τ' σ BC.2) ≃
        globalPairing.NormalizedPair × globalPairing.NormalizedPair :=
    let sigmaProductEquiv :
        (Σ BC : d.1.componentPartition.parts × d.1.componentPartition.parts,
          d.MixedComponentPair τ τ' σ BC.1 × d.MixedComponentPair τ τ' σ BC.2) ≃
          (Σ B : d.1.componentPartition.parts, d.MixedComponentPair τ τ' σ B) ×
            (Σ C : d.1.componentPartition.parts, d.MixedComponentPair τ τ' σ C) := {
      toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
      invFun x := ⟨(x.1.1, x.2.1), (x.1.2, x.2.2)⟩
      left_inv := by rintro ⟨⟨B, C⟩, p, q⟩; rfl
      right_inv := by rintro ⟨⟨B, p⟩, ⟨C, q⟩⟩; rfl }
    sigmaProductEquiv.trans (Equiv.prodCongr pairEquiv pairEquiv)
  rw [globalPairing.crossingCount_eq_sum_crosses,
    ← Equiv.sum_comp componentPairProductEquiv,
    Fintype.sum_sigma, Fintype.sum_prod_type]
  rfl

/-- If every distinct-component geometric crossing count is even, the global mixed crossing count
has the same parity as the sum of the component-internal crossing counts. -/
theorem FixedExternalTwoPointWickDiagram.pairingInMixedOrder_crossingCount_mod_two_eq_sum_components
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hEven : ∀ B C : d.1.componentPartition.parts, B ≠ C →
      d.mixedComponentGeometricCrossingCount τ τ' σ B C % 2 = 0) :
    (d.pairingInMixedOrder τ τ' σ).crossingCount % 2 =
      (∑ B : d.1.componentPartition.parts,
        d.mixedComponentCrossingCount τ τ' σ B) % 2 := by
  rw [d.pairingInMixedOrder_crossingCount_eq_sum_components τ τ' σ]
  exact Combinatorics.fintype_sum_sum_modEq_diag_of_pair_add_modEq_zero
    2 (fun B C => d.mixedComponentOrientedCrossingCount τ τ' σ B C)
    (fun B C hBC => by
      rw [← d.mixedComponentGeometricCrossingCount_eq_oriented_add τ τ' σ B C]
      change d.mixedComponentGeometricCrossingCount τ τ' σ B C % 2 = 0 % 2
      simpa using hEven B C hBC)

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
  classical
  have hparity :=
    d.pairingInMixedOrder_crossingCount_mod_two_eq_sum_components τ τ' σ hEven
  have hpow (t : Finset d.1.componentPartition.parts) :
      (s.zetaInt : ℂ) ^
          (t.sum fun B => d.mixedComponentCrossingCount τ τ' σ B) =
        t.prod fun B => d.mixedComponentWeight s τ τ' σ B := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert B t hB ih =>
        simp [hB, pow_add, FixedExternalTwoPointWickDiagram.mixedComponentWeight, ih]
  calc
    (d.pairingInMixedOrder τ τ' σ).weight s =
        (s.zetaInt : ℂ) ^ (d.pairingInMixedOrder τ τ' σ).crossingCount := rfl
    _ = (s.zetaInt : ℂ) ^
        (∑ B : d.1.componentPartition.parts,
          d.mixedComponentCrossingCount τ τ' σ B) :=
      Common.BlochDeDominicis.zetaInt_pow_eq_of_mod_two_eq s hparity
    _ = ∏ B : d.1.componentPartition.parts,
        d.mixedComponentWeight s τ τ' σ B := by
      simpa using hpow Finset.univ

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

/-- Conditional external/vacuum factorization of the global mixed pairing weight. -/
theorem FixedExternalTwoPointWickDiagram.pairingInMixedOrder_weight_eq_external_mul_prod_vacuum
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (s : Common.Statistics) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hEven : ∀ B C : d.1.componentPartition.parts, B ≠ C →
      d.mixedComponentGeometricCrossingCount τ τ' σ B C % 2 = 0) :
    (d.pairingInMixedOrder τ τ' σ).weight s =
      d.mixedComponentWeight s τ τ' σ d.1.externalComponentPart *
        d.1.vacuumComponentParts.prod
          (d.mixedComponentWeight s τ τ' σ) := by
  rw [d.pairingInMixedOrder_weight_eq_prod_components s τ τ' σ hEven,
    d.prod_mixedComponentWeight_eq_external_mul_prod_vacuum s τ τ' σ]

end Fermionic
end SecondQuantization
