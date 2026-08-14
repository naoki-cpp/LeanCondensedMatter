import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.MixedComponentCrossing
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.MixedComponentPositionTimeTransport

set_option linter.style.header false

/-!
# Transporting mixed component pairs across time assignments

The normalized pairs belonging to one full component form different dependent types for different
mixed-time assignments. Their canonical comparison factors through the time-independent restricted
external or vacuum pairing. Crossing preservation and component-weight covariance are therefore
statistics-independent structural statements.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

/-- Canonical comparison of the mixed normalized pairs of one full component at two time assignments. -/
noncomputable def TwoPointDiagram.mixedComponentPairTimeEquiv
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.componentPartition.parts) :
    d.MixedComponentPair τ τ' σ B ≃ d.MixedComponentPair τ τ' υ B := by
  classical
  by_cases hB : B = d.externalComponentPart
  · subst B
    exact (d.mixedExternalComponentPairEquiv τ τ' σ).trans
      (d.mixedExternalComponentPairEquiv τ τ' υ).symm
  · have hVac : d.ComponentIsVacuum B :=
      (d.componentIsVacuum_iff_ne_externalComponentPart B).2 hB
    exact (d.mixedVacuumComponentPairEquiv τ τ' σ B hVac).trans
      (d.mixedVacuumComponentPairEquiv τ τ' υ B hVac).symm

@[simp]
theorem TwoPointDiagram.mixedComponentPairTimeEquiv_refl
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.componentPartition.parts)
    (pr : d.MixedComponentPair τ τ' σ B) :
    d.mixedComponentPairTimeEquiv τ τ' σ σ B pr = pr := by
  classical
  by_cases hB : B = d.externalComponentPart
  · subst B
    simp [TwoPointDiagram.mixedComponentPairTimeEquiv]
  · simp [TwoPointDiagram.mixedComponentPairTimeEquiv, hB]

/-- The canonical pair transport preserves the component-internal crossing predicate. -/
def TwoPointDiagram.MixedComponentCrossingPreserving
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.componentPartition.parts) : Prop :=
  ∀ p q : d.MixedComponentPair τ τ' σ B,
    Crosses p.1.1 q.1.1 ↔
      Crosses
        (d.mixedComponentPairTimeEquiv τ τ' σ υ B p).1.1
        (d.mixedComponentPairTimeEquiv τ τ' σ υ B q).1.1

/-- Crossing preservation under canonical time transport gives equality of the component-internal
crossing counts. -/
theorem TwoPointDiagram.mixedComponentCrossingCount_eq_of_timeTransport
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.componentPartition.parts)
    (hCross : d.MixedComponentCrossingPreserving τ τ' σ υ B) :
    d.mixedComponentCrossingCount τ τ' σ B =
      d.mixedComponentCrossingCount τ τ' υ B := by
  classical
  let e := d.mixedComponentPairTimeEquiv τ τ' σ υ B
  let ee := Equiv.prodCongr e e
  unfold TwoPointDiagram.mixedComponentCrossingCount
    TwoPointDiagram.mixedComponentOrientedCrossingCount
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
theorem TwoPointDiagram.mixedComponentWeight_eq_of_timeTransport
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (s : Statistics) (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.componentPartition.parts)
    (hCross : d.MixedComponentCrossingPreserving τ τ' σ υ B) :
    d.mixedComponentWeight s τ τ' σ B = d.mixedComponentWeight s τ τ' υ B := by
  unfold TwoPointDiagram.mixedComponentWeight
  rw [d.mixedComponentCrossingCount_eq_of_timeTransport τ τ' σ υ B hCross]

end Common
end SecondQuantization
