import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedComponentPairEquiv
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
    (Equiv.sigmaFiberEquiv (d.mixedPairComponent τ τ' σ)) B C

/-- Crossing count internal to one mixed-time component. -/
noncomputable def TwoPointDiagram.mixedComponentCrossingCount
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.componentPartition.parts) : ℕ :=
  d.mixedComponentOrientedCrossingCount τ τ' σ B B

/-- Exchange-statistics weight associated with crossings internal to one mixed-time component. -/
noncomputable def TwoPointDiagram.mixedComponentWeight
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (s : Statistics) (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.componentPartition.parts) : ℂ :=
  (s.zetaInt : ℂ) ^ d.mixedComponentCrossingCount τ τ' σ B


end Common
end SecondQuantization
