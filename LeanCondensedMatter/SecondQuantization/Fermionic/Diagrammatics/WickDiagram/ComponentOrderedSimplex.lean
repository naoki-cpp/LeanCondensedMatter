import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ComponentOrderedSimplex
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentOrder

set_option linter.style.header false

/-!
# Fermionic component-shuffle ordered-simplex integrands

Thin public aliases for the statistics-independent component-time restriction and shuffled-integrand
API used by quartic Wick diagrams.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} {N : ℕ}

/-- Restrict an ambient fermionic Wick-diagram time assignment to one component's local slots. -/
abbrev QuarticWickDiagram.componentTimeAssignment {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (shuffle : d.ComponentShuffle)
    (τ : Fin S.card → ℝ) (B : d.componentPartition.parts) :
    Fin (B : Finset (Fin N)).card → ℝ :=
  Common.QuarticDiagram.componentTimeAssignment d shuffle τ B

/-- Fermionic component-time restriction is continuous in the ambient time assignment. -/
theorem QuarticWickDiagram.continuous_componentTimeAssignment {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts) :
    Continuous (fun τ : Fin S.card → ℝ => d.componentTimeAssignment shuffle τ B) :=
  Common.QuarticDiagram.continuous_componentTimeAssignment d shuffle B

/-- Product of fermionic component-local integrands embedded by an order-preserving shuffle. -/
noncomputable abbrev QuarticWickDiagram.componentShuffleIntegrand {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (shuffle : d.ComponentShuffle)
    (componentIntegrand :
      ∀ B : d.componentPartition.parts, (Fin (B : Finset (Fin N)).card → ℝ) → ℂ)
    (τ : Fin S.card → ℝ) : ℂ :=
  Common.QuarticDiagram.componentShuffleIntegrand d shuffle componentIntegrand τ

/-- A shuffled product of continuous fermionic component integrands is continuous. -/
theorem QuarticWickDiagram.continuous_componentShuffleIntegrand {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (shuffle : d.ComponentShuffle)
    (componentIntegrand :
      ∀ B : d.componentPartition.parts, (Fin (B : Finset (Fin N)).card → ℝ) → ℂ)
    (hcomponent : ∀ B, Continuous (componentIntegrand B)) :
    Continuous (d.componentShuffleIntegrand shuffle componentIntegrand) :=
  Common.QuarticDiagram.continuous_componentShuffleIntegrand
    d shuffle componentIntegrand hcomponent

/-- The finite fermionic component-shuffle sum commutes with the ambient ordered-simplex integral. -/
theorem QuarticWickDiagram.orderedSimplexIntegral_sum_componentShuffleIntegrand
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) (β : ℝ)
    (componentIntegrand :
      ∀ B : d.componentPartition.parts, (Fin (B : Finset (Fin N)).card → ℝ) → ℂ)
    (hcomponent : ∀ B, Continuous (componentIntegrand B)) :
    intervalIntegral.orderedSimplexIntegral S.card β
        (fun τ => ∑ shuffle : d.ComponentShuffle,
          d.componentShuffleIntegrand shuffle componentIntegrand τ) =
      ∑ shuffle : d.ComponentShuffle,
        intervalIntegral.orderedSimplexIntegral S.card β
          (d.componentShuffleIntegrand shuffle componentIntegrand) :=
  Common.QuarticDiagram.orderedSimplexIntegral_sum_componentShuffleIntegrand
    d β componentIntegrand hcomponent

end Fermionic
end SecondQuantization
