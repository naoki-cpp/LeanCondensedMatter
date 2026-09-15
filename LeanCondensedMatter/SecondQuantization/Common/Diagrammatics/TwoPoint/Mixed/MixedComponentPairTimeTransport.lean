import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Components.ComponentDecomposition
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedComponentPairEquiv

set_option linter.style.header false

/-!
# Transporting mixed component pairs across time assignments

The normalized pairs belonging to one full component form different dependent types for different
mixed-time assignments. Their canonical comparison factors through the time-independent restricted
external or vacuum pairing. This module owns only that pairing-specific transport.
-/

namespace SecondQuantization
namespace Common

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

end Common
end SecondQuantization
