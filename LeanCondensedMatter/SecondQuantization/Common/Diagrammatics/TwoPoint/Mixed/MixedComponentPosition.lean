import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.TwoPointMixedLegOrder
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Components.ComponentRestriction
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.External.ExternalSlotSplit

set_option linter.style.header false

/-!
# Statistics-independent mixed-time component positions

A mixed-time atomic ordering only changes the enumeration of the fixed external-plus-interaction
legs of a two-point diagram. This module transports mixed positions back to the standard diagram-leg
enumeration, assigns them to full graph components, and identifies each component-position fiber
with the corresponding standard component-leg fiber.

The construction depends only on the Common two-point diagram, its pairing-induced components, and
the Common mixed leg order. It contains no operator realization, contraction kernel, Gibbs state, or
particle-statistics choice.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*}

/-- The standard diagram-leg position underlying a mixed-time atomic position. -/
noncomputable def mixedTimeAmbientPositionEquiv {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    Fin (2 * (2 * n + 1)) ≃
      Fin (2 * (2 * (Finset.univ : Finset (Fin n)).card + 1)) :=
  (standardToMixedAtomicPositionEquiv τ τ' σ).symm.trans (finCongr (by simp))

/-- Unflattening the standard ambient position underlying a mixed position recovers the atomic leg
identity stored at that mixed position. -/
theorem twoPointLegEquiv_mixedTimeAmbientPositionEquiv {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) (p : Fin (2 * (2 * n + 1))) :
    twoPointLegEquiv (Finset.univ : Finset (Fin n))
        (mixedTimeAmbientPositionEquiv τ τ' σ p) =
      mixedTimeOrderedAtomicLegEquiv τ τ' σ p := by
  unfold mixedTimeAmbientPositionEquiv standardToMixedAtomicPositionEquiv
  rw [← (twoPointLegEquiv (Finset.univ : Finset (Fin n))).apply_symm_apply
    (mixedTimeOrderedAtomicLegEquiv τ τ' σ p)]
  apply congrArg (twoPointLegEquiv (Finset.univ : Finset (Fin n)))
  apply Fin.ext
  rfl

/-- The full diagram component containing one mixed-time atomic position. -/
noncomputable def TwoPointDiagram.mixedPositionComponent {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (p : Fin (2 * (2 * n + 1))) :
    d.componentPartition.parts :=
  ⟨d.componentBlock
      (twoPointVertexOfLeg (mixedTimeAmbientPositionEquiv τ τ' σ p)),
    d.componentBlock_mem_componentPartition _⟩

/-- Equality with a mixed-position component is exactly standard component-leg membership after
transport back from mixed time order. -/
theorem TwoPointDiagram.mixedPositionComponent_eq_iff_legInComponent {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.componentPartition.parts)
    (p : Fin (2 * (2 * n + 1))) :
    d.mixedPositionComponent τ τ' σ p = B ↔
      d.legInComponent (B : Finset (TwoPointVertex
        (Finset.univ : Finset (Fin n))))
        (mixedTimeAmbientPositionEquiv τ τ' σ p) := by
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    exact h

/-- Mixed-time positions belonging to one full diagram component. -/
abbrev TwoPointDiagram.MixedComponentPosition {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.componentPartition.parts) :=
  {p : Fin (2 * (2 * n + 1)) // d.mixedPositionComponent τ τ' σ p = B}

/-- Positions of one mixed-time component are equivalent to the standard flattened legs of that
component. -/
noncomputable def TwoPointDiagram.mixedComponentPositionEquiv {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.componentPartition.parts) :
    d.MixedComponentPosition τ τ' σ B ≃ d.ComponentLeg B :=
  (mixedTimeAmbientPositionEquiv τ τ' σ).subtypeEquiv fun p =>
    d.mixedPositionComponent_eq_iff_legInComponent τ τ' σ B p

/-- Mixed positions in the external component, reindexed by the canonical left external split. -/
noncomputable def TwoPointDiagram.mixedExternalPositionEquiv {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    d.MixedComponentPosition τ τ' σ d.externalComponentPart ≃
      Fin (2 * (2 * (TwoPointDiagram.interactionPart
        (d.externalComponent 0)).card + 1)) :=
  (d.mixedComponentPositionEquiv τ τ' σ d.externalComponentPart).trans
    d.externalComponentLegEquiv.symm

/-- Mixed positions in a vacuum component, reindexed as the legs of its restricted quartic
diagram. -/
noncomputable def TwoPointDiagram.mixedVacuumPositionEquiv {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.componentPartition.parts)
    (hVac : d.ComponentIsVacuum B) :
    d.MixedComponentPosition τ τ' σ B ≃
      Fin (2 * (2 * (TwoPointDiagram.interactionPart
        (B : Finset (TwoPointVertex
          (Finset.univ : Finset (Fin n))))).card)) :=
  (d.mixedComponentPositionEquiv τ τ' σ B).trans
    (d.vacuumBlockLegEquiv B hVac)

end Common
end SecondQuantization
