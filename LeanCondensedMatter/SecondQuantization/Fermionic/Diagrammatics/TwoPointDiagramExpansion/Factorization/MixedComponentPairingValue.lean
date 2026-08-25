import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Factorization.MixedComponentCrossingEven
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Semantics.PairContraction

set_option linter.style.header false

/-!
# Component-local mixed-time pairing values

Common owns mixed component pair fibers, crossing counts, and statistics weights. The canonical
fixed-external pair contraction is owned by the semantic pair-contraction layer; this module combines
it with the fermionic component weight before feeding the resulting component value downstream.
-/

namespace SecondQuantization
namespace Fermionic

open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Fermionic crossing weight times the contraction product internal to one full component. -/
@[implicit_reducible]
noncomputable def FixedExternalTwoPointWickDiagram.mixedComponentPairingValue
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B : d.1.componentPartition.parts) : ℂ :=
  d.1.mixedComponentWeight Common.Statistics.fermion τ τ' σ B *
    ∏ pr : d.1.MixedComponentPair τ τ' σ B,
      d.mixedPairContractionValue ε β τ τ' σ pr.1

end Fermionic
end SecondQuantization
