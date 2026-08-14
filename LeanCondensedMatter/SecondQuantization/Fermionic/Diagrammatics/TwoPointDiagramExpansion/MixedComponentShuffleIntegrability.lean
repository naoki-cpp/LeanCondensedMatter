import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentOrderedSimplexMeasurable
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentIntegrability

set_option linter.style.header false

/-!
# Measurable bounded shuffle identity for localized mixed component factors

The actual localized component factors are finite measurable selections of globally continuous
fixed-signature representatives.  Hence they satisfy the measurable-local-boundedness interface of
the generalized ordered-simplex shuffle theorem, with no global continuity assumption on the raw
factor across mixed-order walls.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Every canonical localized Dyson-signed component factor satisfies the reusable measurable local
boundedness interface required by the generalized ordered-simplex shuffle theorem. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentDysonLocalIntegrand_measurableLocallyBounded
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (shuffle : d.1.ComponentInteractionShuffle)
    (B : d.1.componentPartition.parts) :
    intervalIntegral.MeasurableLocallyBounded
      (d.mixedComponentDysonLocalIntegrand ε β g τ τ' shuffle B) := by
  apply intervalIntegral.measurableLocallyBounded_of_finite_continuous_selection
    (g := fun s : TwoPointOrderSignature n =>
      d.mixedComponentDysonLocalChamberRepresentative ε β g τ τ'
        (twoPointOrderSignatureBase τ τ' s) shuffle B)
  · exact d.measurable_mixedComponentDysonLocalIntegrand ε β g τ τ' shuffle B
  · intro s
    exact d.continuous_mixedComponentDysonLocalChamberRepresentative
      ε β g τ τ' (twoPointOrderSignatureBase τ τ' s) shuffle B
  · intro localTime
    exact d.exists_mixedComponentDysonLocalChamberRepresentative_eq
      ε β g τ τ' shuffle B localTime

/-- The localized signed component integrands satisfy the finite-family ordered-simplex shuffle
product identity with no externally supplied continuity assumption. -/
theorem FixedExternalTwoPointWickDiagram.sum_mixedComponentDysonLocalIntegral_eq_prod
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (baseShuffle : d.1.ComponentInteractionShuffle) :
    (∑ shuffle : d.1.ComponentInteractionShuffle,
      intervalIntegral.orderedSimplexIntegral
        (Finset.univ : Finset (Fin n)).card β
        (d.1.interactionComponentShuffleIntegrand shuffle
          (d.mixedComponentDysonLocalIntegrand ε β g τ τ' baseShuffle))) =
      ∏ B : d.1.componentPartition.parts,
        intervalIntegral.orderedSimplexIntegral
          (d.1.interactionComponentSize B) β
          (d.mixedComponentDysonLocalIntegrand ε β g τ τ' baseShuffle B) := by
  exact d.1.sum_componentShuffleIntegral_eq_prod_of_measurableLocallyBounded
    β (d.mixedComponentDysonLocalIntegrand ε β g τ τ' baseShuffle)
    (fun B => d.mixedComponentDysonLocalIntegrand_measurableLocallyBounded
      ε β g τ τ' baseShuffle B)

end Fermionic
end SecondQuantization
