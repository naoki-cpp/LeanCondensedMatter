import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentPairEquiv
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedPositionLeg

set_option linter.style.header false

/-!
# Transporting mixed component positions across interaction-time assignments

The mixed-time atomic position occupied by a fixed diagram leg depends on the complete interaction-
time assignment.  Positions belonging to one full component can nevertheless be compared
canonically by transporting them through the time-independent standard component-leg fiber.

This file defines that transport and proves that it preserves the underlying standard ambient
position and atomic leg identity.  The external and vacuum restricted position coordinates are
preserved as well.  These statements are the common coordinate layer needed to prove locality of
component-internal crossings and finite Gibbs pair contractions.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*}

/-- Canonical comparison of mixed positions of one full component at two interaction-time
assignments.  The comparison passes through the fixed standard component-leg fiber. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedComponentPositionTimeEquiv
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.1.componentPartition.parts) :
    d.MixedComponentPosition τ τ' σ B ≃ d.MixedComponentPosition τ τ' υ B :=
  (d.mixedComponentPositionEquiv τ τ' σ B).trans
    (d.mixedComponentPositionEquiv τ τ' υ B).symm

@[simp]
theorem FixedExternalTwoPointWickDiagram.mixedComponentPositionTimeEquiv_refl
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.1.componentPartition.parts)
    (p : d.MixedComponentPosition τ τ' σ B) :
    d.mixedComponentPositionTimeEquiv τ τ' σ σ B p = p := by
  simp [FixedExternalTwoPointWickDiagram.mixedComponentPositionTimeEquiv]

@[simp]
theorem FixedExternalTwoPointWickDiagram.mixedComponentPositionTimeEquiv_symm_apply
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.1.componentPartition.parts)
    (p : d.MixedComponentPosition τ τ' σ B) :
    d.mixedComponentPositionTimeEquiv τ τ' υ σ B
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p) = p := by
  simp [FixedExternalTwoPointWickDiagram.mixedComponentPositionTimeEquiv]

/-- Reading the standard component leg after time transport recovers the original standard
component leg. -/
@[simp]
theorem FixedExternalTwoPointWickDiagram.mixedComponentPositionEquiv_timeEquiv
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.1.componentPartition.parts)
    (p : d.MixedComponentPosition τ τ' σ B) :
    d.mixedComponentPositionEquiv τ τ' υ B
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p) =
      d.mixedComponentPositionEquiv τ τ' σ B p := by
  simp [FixedExternalTwoPointWickDiagram.mixedComponentPositionTimeEquiv]

/-- Time transport preserves the underlying position in the standard flattened diagram-leg
enumeration. -/
theorem FixedExternalTwoPointWickDiagram.mixedTimeAmbientPositionEquiv_positionTimeEquiv
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.1.componentPartition.parts)
    (p : d.MixedComponentPosition τ τ' σ B) :
    mixedTimeAmbientPositionEquiv τ τ' υ
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p).1 =
      mixedTimeAmbientPositionEquiv τ τ' σ p.1 := by
  have h := congrArg Subtype.val
    (d.mixedComponentPositionEquiv_timeEquiv τ τ' σ υ B p)
  change mixedTimeAmbientPositionEquiv τ τ' υ
      (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p).1 =
    mixedTimeAmbientPositionEquiv τ τ' σ p.1 at h
  exact h

/-- Time transport preserves the standard atomic leg identity represented by a mixed component
position. -/
theorem FixedExternalTwoPointWickDiagram.mixedTimeOrderedAtomicLegEquiv_positionTimeEquiv
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.1.componentPartition.parts)
    (p : d.MixedComponentPosition τ τ' σ B) :
    mixedTimeOrderedAtomicLegEquiv τ τ' υ
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p).1 =
      mixedTimeOrderedAtomicLegEquiv τ τ' σ p.1 := by
  rw [← twoPointLegEquiv_mixedTimeAmbientPositionEquiv,
    ← twoPointLegEquiv_mixedTimeAmbientPositionEquiv]
  exact congrArg (Common.twoPointLegEquiv (Finset.univ : Finset (Fin n)))
    (d.mixedTimeAmbientPositionEquiv_positionTimeEquiv τ τ' σ υ B p)

/-- External-component restricted position coordinates are unchanged by time transport. -/
@[simp]
theorem FixedExternalTwoPointWickDiagram.mixedExternalPositionEquiv_positionTimeEquiv
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ υ : Fin n → ℝ)
    (p : d.MixedComponentPosition τ τ' σ d.1.externalComponentPart) :
    d.mixedExternalPositionEquiv τ τ' υ
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ d.1.externalComponentPart p) =
      d.mixedExternalPositionEquiv τ τ' σ p := by
  simp [FixedExternalTwoPointWickDiagram.mixedExternalPositionEquiv,
    FixedExternalTwoPointWickDiagram.mixedComponentPositionTimeEquiv]

/-- Vacuum-component restricted position coordinates are unchanged by time transport. -/
@[simp]
theorem FixedExternalTwoPointWickDiagram.mixedVacuumPositionEquiv_positionTimeEquiv
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.1.componentPartition.parts)
    (hVac : d.1.ComponentIsVacuum B)
    (p : d.MixedComponentPosition τ τ' σ B) :
    d.mixedVacuumPositionEquiv τ τ' υ B hVac
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p) =
      d.mixedVacuumPositionEquiv τ τ' σ B hVac p := by
  simp [FixedExternalTwoPointWickDiagram.mixedVacuumPositionEquiv,
    FixedExternalTwoPointWickDiagram.mixedComponentPositionTimeEquiv]

end Fermionic
end SecondQuantization
