import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentOrderedSimplex
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentIntegrability

set_option linter.style.header false

/-!
# Measurable bounded shuffle identity for localized mixed component factors

The actual localized component factors are finite measurable selections of globally continuous
fixed-signature representatives. Hence they satisfy the measurable-local-boundedness interface of
the generic finite-family ordered-simplex shuffle theorem, with no global continuity assumption on
the raw factor across mixed-order walls.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Every canonical localized Dyson-signed component factor satisfies measurable local boundedness. -/
private theorem mixedComponentDysonLocalIntegrand_measurableLocallyBounded
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
  change
    (∑ shuffle : FamilySlotShuffleTo d.1.interactionComponentSize
        (Finset.univ : Finset (Fin n)).card,
      intervalIntegral.orderedSimplexIntegral
        (Finset.univ : Finset (Fin n)).card β
        (shuffle.ambientIntegrand
          (d.mixedComponentDysonLocalIntegrand ε β g τ τ' baseShuffle))) =
      ∏ B : d.1.componentPartition.parts,
        intervalIntegral.orderedSimplexIntegral
          (d.1.interactionComponentSize B) β
          (d.mixedComponentDysonLocalIntegrand ε β g τ τ' baseShuffle B)
  exact
    FamilySlotShuffleTo.sum_orderedSimplexIntegral_ambientIntegrand_eq_prod_fintype_of_measurableLocallyBounded
      (ι := d.1.componentPartition.parts) d.1.interactionComponentSize
      (Finset.univ : Finset (Fin n)).card d.1.sum_interactionComponentSize β
      (d.mixedComponentDysonLocalIntegrand ε β g τ τ' baseShuffle)
      (fun B => mixedComponentDysonLocalIntegrand_measurableLocallyBounded
        d ε β g τ τ' baseShuffle B)

end Fermionic
end SecondQuantization
