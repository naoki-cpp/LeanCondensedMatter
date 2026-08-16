import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentCrossingEven
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Reindexing
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Pairing
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Amplitude

set_option linter.style.header false

/-!
# Component-local mixed-time pairing values

Common owns mixed component pair fibers, crossing counts, and statistics weights. This module owns
the canonical fixed-external pair contraction and combines it with the fermionic component weight
before feeding the resulting component value into the fixed-time amplitude.
-/

namespace SecondQuantization
namespace Fermionic

open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Canonical free Gibbs density-state contraction attached to one normalized pair in the actual
mixed-time pairing. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedPairContractionValue
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (pr : (d.1.pairingInMixedOrder τ τ' σ).NormalizedPair) : ℂ :=
  mixedTimeOrderedAtomicPairValue ε β i j τ τ' σ d.vertexLabelSequence
    pr.1.1 pr.1.2

/-- Fermionic crossing weight times the contraction product internal to one full component. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedComponentPairingValue
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B : d.1.componentPartition.parts) : ℂ :=
  d.1.mixedComponentWeight Common.Statistics.fermion τ τ' σ B *
    ∏ pr : d.1.MixedComponentPair τ τ' σ B,
      d.mixedPairContractionValue ε β τ τ' σ pr.1

end Fermionic
end SecondQuantization
