import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.MixedComponentPairTimeTransport
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.MixedComponentTimeTransport

set_option linter.style.header false

/-!
# Endpoint behavior of mixed component pair transport

Canonical pair transport across time assignments factors through the restricted external or vacuum
pairing, while #1206 position transport factors through the standard component-leg fiber. Their
endpoint coordinates agree up to normalized-pair swap, and agree exactly whenever component
position order is preserved.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

@[simp]
private theorem TwoPointDiagram.mixedExternalComponentPairEquiv_pairTimeEquiv
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ)
    (pr : d.MixedComponentPair τ τ' σ d.externalComponentPart) :
    d.mixedExternalComponentPairEquiv τ τ' υ
        (d.mixedComponentPairTimeEquiv τ τ' σ υ d.externalComponentPart pr) =
      d.mixedExternalComponentPairEquiv τ τ' σ pr := by
  simp [TwoPointDiagram.mixedComponentPairTimeEquiv]

@[simp]
private theorem TwoPointDiagram.mixedVacuumComponentPairEquiv_pairTimeEquiv
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.componentPartition.parts)
    (hVac : d.ComponentIsVacuum B)
    (pr : d.MixedComponentPair τ τ' σ B) :
    d.mixedVacuumComponentPairEquiv τ τ' υ B hVac
        (d.mixedComponentPairTimeEquiv τ τ' σ υ B pr) =
      d.mixedVacuumComponentPairEquiv τ τ' σ B hVac pr := by
  have hB : B ≠ d.externalComponentPart :=
    (d.componentIsVacuum_iff_ne_externalComponentPart B).1 hVac
  simp [TwoPointDiagram.mixedComponentPairTimeEquiv, hB]

/-- Pair-time transport sends endpoints to the position-time transports of the original endpoints,
either in the same normalized order or swapped. -/
private theorem TwoPointDiagram.mixedComponentPairTimeEquiv_endpoints_eq_or_swap
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.componentPartition.parts)
    (pr : d.MixedComponentPair τ τ' σ B) :
    let q := d.mixedComponentPairTimeEquiv τ τ' σ υ B pr
    (d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 0) =
          d.mixedComponentPositionTimeEquiv τ τ' σ υ B
            (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0)) ∧
        d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 1) =
          d.mixedComponentPositionTimeEquiv τ τ' σ υ B
            (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1))) ∨
      (d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 0) =
          d.mixedComponentPositionTimeEquiv τ τ' σ υ B
            (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1)) ∧
        d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 1) =
          d.mixedComponentPositionTimeEquiv τ τ' σ υ B
            (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0))) := by
  classical
  dsimp only
  by_cases hB : B = d.externalComponentPart
  · subst B
    let q := d.mixedComponentPairTimeEquiv τ τ' σ υ d.externalComponentPart pr
    have hlocal :
        d.mixedExternalComponentPairEquiv τ τ' υ q =
          d.mixedExternalComponentPairEquiv τ τ' σ pr := by
      simpa [q] using d.mixedExternalComponentPairEquiv_pairTimeEquiv τ τ' σ υ pr
    have hlocalVal :
        (d.mixedExternalComponentPairEquiv τ τ' υ q).1 =
          (d.mixedExternalComponentPairEquiv τ τ' σ pr).1 :=
      congrArg Subtype.val hlocal
    rcases d.mixedExternalComponentPairEquiv_pair_eq_or_swap τ τ' σ pr with hp | hp <;>
      rcases d.mixedExternalComponentPairEquiv_pair_eq_or_swap τ τ' υ q with hq | hq
    · left
      have hcoords := hq.symm.trans (hlocalVal.trans hp)
      constructor
      · apply (d.mixedExternalPositionEquiv τ τ' υ).injective
        simpa using congrArg Prod.fst hcoords
      · apply (d.mixedExternalPositionEquiv τ τ' υ).injective
        simpa using congrArg Prod.snd hcoords
    · right
      have hcoords := hq.symm.trans (hlocalVal.trans hp)
      constructor
      · apply (d.mixedExternalPositionEquiv τ τ' υ).injective
        simpa using congrArg Prod.snd hcoords
      · apply (d.mixedExternalPositionEquiv τ τ' υ).injective
        simpa using congrArg Prod.fst hcoords
    · right
      have hcoords := hq.symm.trans (hlocalVal.trans hp)
      constructor
      · apply (d.mixedExternalPositionEquiv τ τ' υ).injective
        simpa using congrArg Prod.fst hcoords
      · apply (d.mixedExternalPositionEquiv τ τ' υ).injective
        simpa using congrArg Prod.snd hcoords
    · left
      have hcoords := hq.symm.trans (hlocalVal.trans hp)
      constructor
      · apply (d.mixedExternalPositionEquiv τ τ' υ).injective
        simpa using congrArg Prod.snd hcoords
      · apply (d.mixedExternalPositionEquiv τ τ' υ).injective
        simpa using congrArg Prod.fst hcoords
  · have hVac : d.ComponentIsVacuum B :=
      (d.componentIsVacuum_iff_ne_externalComponentPart B).2 hB
    let q := d.mixedComponentPairTimeEquiv τ τ' σ υ B pr
    have hlocal :
        d.mixedVacuumComponentPairEquiv τ τ' υ B hVac q =
          d.mixedVacuumComponentPairEquiv τ τ' σ B hVac pr := by
      simpa [q] using d.mixedVacuumComponentPairEquiv_pairTimeEquiv τ τ' σ υ B hVac pr
    have hlocalVal :
        (d.mixedVacuumComponentPairEquiv τ τ' υ B hVac q).1 =
          (d.mixedVacuumComponentPairEquiv τ τ' σ B hVac pr).1 :=
      congrArg Subtype.val hlocal
    rcases d.mixedVacuumComponentPairEquiv_pair_eq_or_swap τ τ' σ B hVac pr with hp | hp <;>
      rcases d.mixedVacuumComponentPairEquiv_pair_eq_or_swap τ τ' υ B hVac q with hq | hq
    · left
      have hcoords := hq.symm.trans (hlocalVal.trans hp)
      constructor
      · apply (d.mixedVacuumPositionEquiv τ τ' υ B hVac).injective
        simpa using congrArg Prod.fst hcoords
      · apply (d.mixedVacuumPositionEquiv τ τ' υ B hVac).injective
        simpa using congrArg Prod.snd hcoords
    · right
      have hcoords := hq.symm.trans (hlocalVal.trans hp)
      constructor
      · apply (d.mixedVacuumPositionEquiv τ τ' υ B hVac).injective
        simpa using congrArg Prod.snd hcoords
      · apply (d.mixedVacuumPositionEquiv τ τ' υ B hVac).injective
        simpa using congrArg Prod.fst hcoords
    · right
      have hcoords := hq.symm.trans (hlocalVal.trans hp)
      constructor
      · apply (d.mixedVacuumPositionEquiv τ τ' υ B hVac).injective
        simpa using congrArg Prod.fst hcoords
      · apply (d.mixedVacuumPositionEquiv τ τ' υ B hVac).injective
        simpa using congrArg Prod.snd hcoords
    · left
      have hcoords := hq.symm.trans (hlocalVal.trans hp)
      constructor
      · apply (d.mixedVacuumPositionEquiv τ τ' υ B hVac).injective
        simpa using congrArg Prod.snd hcoords
      · apply (d.mixedVacuumPositionEquiv τ τ' υ B hVac).injective
        simpa using congrArg Prod.fst hcoords

/-- If component position transport preserves strict mixed order, pair-time transport preserves the
normalized endpoint order exactly. -/
theorem TwoPointDiagram.mixedComponentPairTimeEquiv_endpoints_eq_of_positionOrder
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.componentPartition.parts)
    (hOrder : ∀ p q : d.MixedComponentPosition τ τ' σ B,
      p.1 < q.1 ↔
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p).1 <
          (d.mixedComponentPositionTimeEquiv τ τ' σ υ B q).1)
    (pr : d.MixedComponentPair τ τ' σ B) :
    let q := d.mixedComponentPairTimeEquiv τ τ' σ υ B pr
    d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 0) =
        d.mixedComponentPositionTimeEquiv τ τ' σ υ B
          (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0)) ∧
      d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 1) =
        d.mixedComponentPositionTimeEquiv τ τ' σ υ B
          (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1)) := by
  classical
  let q := d.mixedComponentPairTimeEquiv τ τ' σ υ B pr
  change d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 0) = _ ∧
    d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 1) = _
  have hCases :
      (d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 0) =
          d.mixedComponentPositionTimeEquiv τ τ' σ υ B
            (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0)) ∧
        d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 1) =
          d.mixedComponentPositionTimeEquiv τ τ' σ υ B
            (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1))) ∨
      (d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 0) =
          d.mixedComponentPositionTimeEquiv τ τ' σ υ B
            (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1)) ∧
        d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 1) =
          d.mixedComponentPositionTimeEquiv τ τ' σ υ B
            (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0))) := by
    simpa [q] using d.mixedComponentPairTimeEquiv_endpoints_eq_or_swap τ τ' σ υ B pr
  rcases hCases with hSame | hSwap
  · exact hSame
  · have hSource :
        (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0)).1 <
          (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1)).1 :=
      ((d.pairingInMixedOrder τ τ' σ).mem_pairs_iff pr.1.1.1 pr.1.1.2).mp pr.1.2 |>.1
    have hTransport :=
      (hOrder (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0))
        (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1))).1 hSource
    have hTarget :
        (d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 0)).1 <
          (d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 1)).1 :=
      ((d.pairingInMixedOrder τ τ' υ).mem_pairs_iff q.1.1.1 q.1.1.2).mp q.1.2 |>.1
    rw [hSwap.1, hSwap.2] at hTarget
    exact (lt_asymm hTarget hTransport).elim

/-- Under component-local equality of interaction times, canonical pair-time transport preserves the
normalized endpoint order exactly. -/
theorem TwoPointDiagram.mixedComponentPairTimeEquiv_endpoints_eq
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.componentPartition.parts)
    (hTime : d.ComponentTimeEq B σ υ)
    (pr : d.MixedComponentPair τ τ' σ B) :
    let q := d.mixedComponentPairTimeEquiv τ τ' σ υ B pr
    d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 0) =
        d.mixedComponentPositionTimeEquiv τ τ' σ υ B
          (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0)) ∧
      d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 1) =
        d.mixedComponentPositionTimeEquiv τ τ' σ υ B
          (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1)) :=
  d.mixedComponentPairTimeEquiv_endpoints_eq_of_positionOrder τ τ' σ υ B
    (d.mixedComponentPositionTimeEquiv_lt_iff τ τ' σ υ B hTime) pr

end Common
end SecondQuantization
