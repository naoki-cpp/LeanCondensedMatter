import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentShufflePermutation
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentCanonicalLocality

set_option linter.style.header false

/-!
# Component-shuffle permutations for fixed fermionic two-point diagrams

The Common layer shows that every component interaction shuffle differs from the canonical shuffle
by an ambient interaction-slot permutation.  For a fixed fermionic diagram, the canonical shuffled
product is exactly the pointwise Dyson amplitude up to the external ordering sign.  Combining these
facts identifies every non-canonical shuffled product with the canonical component-local product
evaluated on permuted interaction-time coordinates.

This deliberately stops before calling the right-hand side the amplitude of a relabeled diagram:
that requires a separate interaction-vertex relabeling construction carrying labels and pairings.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

private def ambientToTwoPointSlotTimePermutation {n : ℕ}
    (σ : Fin (Finset.univ : Finset (Fin n)).card → ℝ) : Fin n → ℝ :=
  fun i => σ (Fin.cast (by simp) i)

/-- Any component-shuffle integrand of the canonical localized factors is the canonical
component-shuffle integrand after the ambient interaction times are permuted by the shuffle's
ambient permutation. -/
theorem FixedExternalTwoPointWickDiagram.componentShuffleIntegrand_eq_canonical_permuted
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (shuffle : d.1.ComponentInteractionShuffle)
    (σ : Fin (Finset.univ : Finset (Fin n)).card → ℝ) :
    d.1.interactionComponentShuffleIntegrand shuffle
        (d.mixedComponentDysonLocalIntegrand ε β g τ τ'
          d.1.canonicalComponentInteractionShuffle) σ =
      d.1.interactionComponentShuffleIntegrand
        d.1.canonicalComponentInteractionShuffle
        (d.mixedComponentDysonLocalIntegrand ε β g τ τ'
          d.1.canonicalComponentInteractionShuffle)
        (fun k => σ (shuffle.ambientPermutation k)) := by
  exact shuffle.interactionComponentShuffleIntegrand_eq_canonical
    (d.mixedComponentDysonLocalIntegrand ε β g τ τ'
      d.1.canonicalComponentInteractionShuffle) σ

/-- Pointwise, a non-canonical shuffled product is the canonical Dyson amplitude at permuted
interaction times after removing the common external ordering sign.  The theorem is stated with the
sign multiplied on both sides so that no division or nonzero side condition is needed. -/
theorem FixedExternalTwoPointWickDiagram.externalSign_mul_componentShuffleIntegrand_eq_dysonFixedTimeAmplitude_permuted
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (shuffle : d.1.ComponentInteractionShuffle)
    (σ : Fin (Finset.univ : Finset (Fin n)).card → ℝ) :
    twoPointExternalOrderSign τ τ' *
        d.1.interactionComponentShuffleIntegrand shuffle
          (d.mixedComponentDysonLocalIntegrand ε β g τ τ'
            d.1.canonicalComponentInteractionShuffle) σ =
      d.dysonFixedTimeAmplitude ε β g τ τ'
        (ambientToTwoPointSlotTimePermutation
          (fun k => σ (shuffle.ambientPermutation k))) := by
  rw [d.componentShuffleIntegrand_eq_canonical_permuted
    ε β g τ τ' shuffle σ]
  symm
  exact d.dysonFixedTimeAmplitude_eq_canonicalComponentShuffleIntegrand
    ε β g τ τ'
    (ambientToTwoPointSlotTimePermutation
      (fun k => σ (shuffle.ambientPermutation k)))

end Fermionic
end SecondQuantization
