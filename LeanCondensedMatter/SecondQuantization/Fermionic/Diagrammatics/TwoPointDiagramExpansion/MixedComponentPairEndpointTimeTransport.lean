import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentPairTimeTransport
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.MixedComponentTimeTransport

set_option linter.style.header false

/-!
# Endpoint behavior of mixed component pair transport

Pair transport across interaction-time assignments is defined through the time-independent
restricted external or vacuum pairing. Position transport is defined through the time-independent
standard component-leg fiber. This module first proves that the two transports agree on pair
endpoints up to the normalization swap of a `Pairing.NormalizedPair`.

When the interaction times agree on the component, component-position transport preserves strict
order. The normalization swap is then impossible, so pair transport agrees with position transport
on both endpoints in their original order. This is the endpoint-coordinate bridge needed for
preservation of crossings and finite Gibbs contractions.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*}

/-- The restricted external normalized pair is unchanged by canonical pair-time transport. -/
@[simp]
theorem FixedExternalTwoPointWickDiagram.mixedExternalComponentPairEquiv_pairTimeEquiv
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ υ : Fin n → ℝ)
    (pr : d.MixedComponentPair τ τ' σ d.1.externalComponentPart) :
    d.mixedExternalComponentPairEquiv τ τ' υ
        (d.mixedComponentPairTimeEquiv τ τ' σ υ d.1.externalComponentPart pr) =
      d.mixedExternalComponentPairEquiv τ τ' σ pr := by
  simp [FixedExternalTwoPointWickDiagram.mixedComponentPairTimeEquiv]

/-- The restricted vacuum normalized pair is unchanged by canonical pair-time transport. -/
@[simp]
theorem FixedExternalTwoPointWickDiagram.mixedVacuumComponentPairEquiv_pairTimeEquiv
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.1.componentPartition.parts)
    (hVac : d.1.ComponentIsVacuum B)
    (pr : d.MixedComponentPair τ τ' σ B) :
    d.mixedVacuumComponentPairEquiv τ τ' υ B hVac
        (d.mixedComponentPairTimeEquiv τ τ' σ υ B pr) =
      d.mixedVacuumComponentPairEquiv τ τ' σ B hVac pr := by
  have hB : B ≠ d.1.externalComponentPart :=
    (d.1.componentIsVacuum_iff_ne_externalComponentPart B).1 hVac
  simp [FixedExternalTwoPointWickDiagram.mixedComponentPairTimeEquiv, hB]

/-- Canonical pair-time transport sends the two endpoints of a mixed component pair to the
position-time transports of the original endpoints, either in the same normalized order or swapped.
-/
theorem FixedExternalTwoPointWickDiagram.mixedComponentPairTimeEquiv_endpoints_eq_or_swap
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.1.componentPartition.parts)
    (pr : d.MixedComponentPair τ τ' σ B) :
    let q := d.mixedComponentPairTimeEquiv τ τ' σ υ B pr
    (d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 0) =
          d.1.mixedComponentPositionTimeEquiv τ τ' σ υ B
            (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0)) ∧
        d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 1) =
          d.1.mixedComponentPositionTimeEquiv τ τ' σ υ B
            (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1))) ∨
      (d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 0) =
          d.1.mixedComponentPositionTimeEquiv τ τ' σ υ B
            (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1)) ∧
        d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 1) =
          d.1.mixedComponentPositionTimeEquiv τ τ' σ υ B
            (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0))) := by
  classical
  dsimp only
  by_cases hB : B = d.1.externalComponentPart
  · subst B
    let q := d.mixedComponentPairTimeEquiv τ τ' σ υ d.1.externalComponentPart pr
    have hlocal :
        d.mixedExternalComponentPairEquiv τ τ' υ q =
          d.mixedExternalComponentPairEquiv τ τ' σ pr := by
      simpa [q] using
        d.mixedExternalComponentPairEquiv_pairTimeEquiv τ τ' σ υ pr
    have hlocalVal :
        (d.mixedExternalComponentPairEquiv τ τ' υ q).1 =
          (d.mixedExternalComponentPairEquiv τ τ' σ pr).1 :=
      congrArg Subtype.val hlocal
    rcases d.mixedExternalComponentPairEquiv_pair_eq_or_swap τ τ' σ pr with hp | hp <;>
      rcases d.mixedExternalComponentPairEquiv_pair_eq_or_swap τ τ' υ q with hq | hq
    · left
      have hcoords := hq.symm.trans (hlocalVal.trans hp)
      constructor
      · apply (d.1.mixedExternalPositionEquiv τ τ' υ).injective
        simpa using congrArg Prod.fst hcoords
      · apply (d.1.mixedExternalPositionEquiv τ τ' υ).injective
        simpa using congrArg Prod.snd hcoords
    · right
      have hcoords := hq.symm.trans (hlocalVal.trans hp)
      constructor
      · apply (d.1.mixedExternalPositionEquiv τ τ' υ).injective
        simpa using congrArg Prod.snd hcoords
      · apply (d.1.mixedExternalPositionEquiv τ τ' υ).injective
        simpa using congrArg Prod.fst hcoords
    · right
      have hcoords := hq.symm.trans (hlocalVal.trans hp)
      constructor
      · apply (d.1.mixedExternalPositionEquiv τ τ' υ).injective
        simpa using congrArg Prod.fst hcoords
      · apply (d.1.mixedExternalPositionEquiv τ τ' υ).injective
        simpa using congrArg Prod.snd hcoords
    · left
      have hcoords := hq.symm.trans (hlocalVal.trans hp)
      constructor
      · apply (d.1.mixedExternalPositionEquiv τ τ' υ).injective
        simpa using congrArg Prod.snd hcoords
      · apply (d.1.mixedExternalPositionEquiv τ τ' υ).injective
        simpa using congrArg Prod.fst hcoords
  · have hVac : d.1.ComponentIsVacuum B :=
      (d.1.componentIsVacuum_iff_ne_externalComponentPart B).2 hB
    let q := d.mixedComponentPairTimeEquiv τ τ' σ υ B pr
    have hlocal :
        d.mixedVacuumComponentPairEquiv τ τ' υ B hVac q =
          d.mixedVacuumComponentPairEquiv τ τ' σ B hVac pr := by
      simpa [q] using
        d.mixedVacuumComponentPairEquiv_pairTimeEquiv τ τ' σ υ B hVac pr
    have hlocalVal :
        (d.mixedVacuumComponentPairEquiv τ τ' υ B hVac q).1 =
          (d.mixedVacuumComponentPairEquiv τ τ' σ B hVac pr).1 :=
      congrArg Subtype.val hlocal
    rcases d.mixedVacuumComponentPairEquiv_pair_eq_or_swap τ τ' σ B hVac pr with hp | hp <;>
      rcases d.mixedVacuumComponentPairEquiv_pair_eq_or_swap τ τ' υ B hVac q with hq | hq
    · left
      have hcoords := hq.symm.trans (hlocalVal.trans hp)
      constructor
      · apply (d.1.mixedVacuumPositionEquiv τ τ' υ B hVac).injective
        simpa using congrArg Prod.fst hcoords
      · apply (d.1.mixedVacuumPositionEquiv τ τ' υ B hVac).injective
        simpa using congrArg Prod.snd hcoords
    · right
      have hcoords := hq.symm.trans (hlocalVal.trans hp)
      constructor
      · apply (d.1.mixedVacuumPositionEquiv τ τ' υ B hVac).injective
        simpa using congrArg Prod.snd hcoords
      · apply (d.1.mixedVacuumPositionEquiv τ τ' υ B hVac).injective
        simpa using congrArg Prod.fst hcoords
    · right
      have hcoords := hq.symm.trans (hlocalVal.trans hp)
      constructor
      · apply (d.1.mixedVacuumPositionEquiv τ τ' υ B hVac).injective
        simpa using congrArg Prod.fst hcoords
      · apply (d.1.mixedVacuumPositionEquiv τ τ' υ B hVac).injective
        simpa using congrArg Prod.snd hcoords
    · left
      have hcoords := hq.symm.trans (hlocalVal.trans hp)
      constructor
      · apply (d.1.mixedVacuumPositionEquiv τ τ' υ B hVac).injective
        simpa using congrArg Prod.snd hcoords
      · apply (d.1.mixedVacuumPositionEquiv τ τ' υ B hVac).injective
        simpa using congrArg Prod.fst hcoords

/-- Whenever component position transport preserves strict mixed order, canonical pair-time
transport preserves the normalized endpoint order exactly; the swap alternative would reverse the
two endpoints of a normalized pair. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentPairTimeEquiv_endpoints_eq_of_positionOrder
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.1.componentPartition.parts)
    (hOrder : ∀ p q : d.1.MixedComponentPosition τ τ' σ B,
      p.1 < q.1 ↔
        (d.1.mixedComponentPositionTimeEquiv τ τ' σ υ B p).1 <
          (d.1.mixedComponentPositionTimeEquiv τ τ' σ υ B q).1)
    (pr : d.MixedComponentPair τ τ' σ B) :
    let q := d.mixedComponentPairTimeEquiv τ τ' σ υ B pr
    d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 0) =
        d.1.mixedComponentPositionTimeEquiv τ τ' σ υ B
          (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0)) ∧
      d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 1) =
        d.1.mixedComponentPositionTimeEquiv τ τ' σ υ B
          (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1)) := by
  classical
  let q := d.mixedComponentPairTimeEquiv τ τ' σ υ B pr
  change d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 0) = _ ∧
    d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 1) = _
  have hCases :
      (d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 0) =
          d.1.mixedComponentPositionTimeEquiv τ τ' σ υ B
            (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0)) ∧
        d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 1) =
          d.1.mixedComponentPositionTimeEquiv τ τ' σ υ B
            (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1))) ∨
      (d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 0) =
          d.1.mixedComponentPositionTimeEquiv τ τ' σ υ B
            (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1)) ∧
        d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 1) =
          d.1.mixedComponentPositionTimeEquiv τ τ' σ υ B
            (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0))) := by
    simpa [q] using
      d.mixedComponentPairTimeEquiv_endpoints_eq_or_swap τ τ' σ υ B pr
  rcases hCases with hSame | hSwap
  · exact hSame
  · have hSource :
        (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0)).1 <
          (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1)).1 :=
      ((d.pairingInMixedOrder τ τ' σ).mem_pairs_iff
        pr.1.1.1 pr.1.1.2).mp pr.1.2 |>.1
    have hTransport :=
      (hOrder (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0))
        (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1))).1 hSource
    have hTarget :
        (d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 0)).1 <
          (d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 1)).1 :=
      ((d.pairingInMixedOrder τ τ' υ).mem_pairs_iff
        q.1.1.1 q.1.1.2).mp q.1.2 |>.1
    rw [hSwap.1, hSwap.2] at hTarget
    exact (lt_asymm hTarget hTransport).elim

/-- Under component-local equality of interaction times, canonical pair-time transport preserves the
normalized endpoint order exactly; the swap alternative is impossible. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentPairTimeEquiv_endpoints_eq
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.1.componentPartition.parts)
    (hTime : d.1.ComponentTimeEq B σ υ)
    (pr : d.MixedComponentPair τ τ' σ B) :
    let q := d.mixedComponentPairTimeEquiv τ τ' σ υ B pr
    d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 0) =
        d.1.mixedComponentPositionTimeEquiv τ τ' σ υ B
          (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0)) ∧
      d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 1) =
        d.1.mixedComponentPositionTimeEquiv τ τ' σ υ B
          (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1)) :=
  d.mixedComponentPairTimeEquiv_endpoints_eq_of_positionOrder τ τ' σ υ B
    (d.1.mixedComponentPositionTimeEquiv_lt_iff τ τ' σ υ B hTime) pr

end Fermionic
end SecondQuantization
