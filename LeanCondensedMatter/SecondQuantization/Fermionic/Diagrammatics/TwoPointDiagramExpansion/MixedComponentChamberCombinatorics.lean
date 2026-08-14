import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.MixedComponentTimeTransport
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentCrossingTimeLocality

set_option linter.style.header false

/-!
# Mixed component pairing combinatorics on fixed order chambers

Common owns the chamber-invariance of mixed atomic-leg order and component-position transport. This
module retains the pairing-specific consequences for normalized pair endpoints, component crossings,
and Statistics-parametric pairing weights.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*}

theorem FixedExternalTwoPointWickDiagram.mixedComponentPairTimeEquiv_endpoints_eq_of_sameOrderChamber
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.1.componentPartition.parts)
    (hChamber : SameTwoPointOrderChamber τ τ' σ υ)
    (pr : d.MixedComponentPair τ τ' σ B) :
    let q := d.mixedComponentPairTimeEquiv τ τ' σ υ B pr
    d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 0) =
        d.1.mixedComponentPositionTimeEquiv τ τ' σ υ B
          (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0)) ∧
      d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 1) =
        d.1.mixedComponentPositionTimeEquiv τ τ' σ υ B
          (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1)) :=
  d.mixedComponentPairTimeEquiv_endpoints_eq_of_positionOrder τ τ' σ υ B
    (d.1.mixedComponentPositionTimeEquiv_lt_iff_of_sameOrderChamber
      τ τ' σ υ B hChamber) pr

theorem FixedExternalTwoPointWickDiagram.mixedComponentCrossingPreserving_of_sameOrderChamber
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.1.componentPartition.parts)
    (hChamber : SameTwoPointOrderChamber τ τ' σ υ) :
    d.MixedComponentCrossingPreserving τ τ' σ υ B :=
  d.mixedComponentCrossingPreserving_of_positionOrder τ τ' σ υ B
    (d.1.mixedComponentPositionTimeEquiv_lt_iff_of_sameOrderChamber
      τ τ' σ υ B hChamber)

theorem FixedExternalTwoPointWickDiagram.mixedComponentCrossingCount_eq_of_sameOrderChamber
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.1.componentPartition.parts)
    (hChamber : SameTwoPointOrderChamber τ τ' σ υ) :
    d.mixedComponentCrossingCount τ τ' σ B =
      d.mixedComponentCrossingCount τ τ' υ B :=
  d.mixedComponentCrossingCount_eq_of_timeTransport τ τ' σ υ B
    (d.mixedComponentCrossingPreserving_of_sameOrderChamber
      τ τ' σ υ B hChamber)

theorem FixedExternalTwoPointWickDiagram.mixedComponentWeight_eq_of_sameOrderChamber
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (s : Common.Statistics) (τ τ' : ℝ) (σ υ : Fin n → ℝ)
    (B : d.1.componentPartition.parts)
    (hChamber : SameTwoPointOrderChamber τ τ' σ υ) :
    d.mixedComponentWeight s τ τ' σ B =
      d.mixedComponentWeight s τ τ' υ B :=
  d.mixedComponentWeight_eq_of_timeTransport s τ τ' σ υ B
    (d.mixedComponentCrossingPreserving_of_sameOrderChamber
      τ τ' σ υ B hChamber)

end Fermionic
end SecondQuantization
