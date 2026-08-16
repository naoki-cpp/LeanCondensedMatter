import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Reindexing
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Pairing
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.MixedComponentPairProduct

set_option linter.style.header false

/-!
# Fermionic contraction products over mixed two-point components

Common owns the mixed-pair component fibers and their generic commutative-product factorization.
This module adds only the canonical free Gibbs contraction values used by the component-local
fermionic amplitudes.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
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

end Fermionic
end SecondQuantization
