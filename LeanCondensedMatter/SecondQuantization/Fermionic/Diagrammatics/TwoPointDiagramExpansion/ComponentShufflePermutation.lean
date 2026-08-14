import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentShufflePermutation
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentCanonicalLocality
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.InteractionVertexRelabel

set_option linter.style.header false

/-!
# Component-shuffle permutations for fixed fermionic two-point diagrams

The Common layer owns the ambient component-shuffle permutation, its transport from `Fin univ.card`
to the explicit interaction-slot type `Fin n`, and the corresponding standard two-point diagram
relabeling. This file only lifts that relabeling through the fixed fermionic external-label subtype
and connects the Common shuffle transport to fermionic Dyson amplitudes and external-order signs.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Lift the Common component-shuffle relabeling through the fixed external-label subtype. -/
noncomputable def FixedExternalTwoPointWickDiagram.relabelForComponentShuffle
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (shuffle : d.1.ComponentInteractionShuffle) : FixedExternalTwoPointWickDiagram Mode n i j :=
  ⟨d.1.relabelForComponentShuffle shuffle, by simpa using d.2⟩

omit [LinearOrder Mode] [Fintype Mode] in
@[simp]
theorem FixedExternalTwoPointWickDiagram.relabelForComponentShuffle_vertexLabelSequence
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (shuffle : d.1.ComponentInteractionShuffle) (v : Fin n) :
    (d.relabelForComponentShuffle shuffle).vertexLabelSequence v =
      d.vertexLabelSequence ((d.1.componentShuffleSlotPermutation shuffle).symm v) :=
  rfl

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
interaction times after removing the common external ordering sign. The theorem is stated with the
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

/-- The shuffled pointwise product is the fixed-diagram Dyson amplitude after the same shuffle is
expressed directly as a permutation of the explicit `Fin n` interaction slots. -/
theorem FixedExternalTwoPointWickDiagram.externalSign_mul_componentShuffleIntegrand_eq_dysonFixedTimeAmplitude_slotPermuted
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (shuffle : d.1.ComponentInteractionShuffle)
    (σ : Fin (Finset.univ : Finset (Fin n)).card → ℝ) :
    twoPointExternalOrderSign τ τ' *
        d.1.interactionComponentShuffleIntegrand shuffle
          (d.mixedComponentDysonLocalIntegrand ε β g τ τ'
            d.1.canonicalComponentInteractionShuffle) σ =
      d.dysonFixedTimeAmplitude ε β g τ τ'
        (fun v => ambientToTwoPointSlotTimePermutation σ
          (d.1.componentShuffleSlotPermutation shuffle v)) := by
  rw [d.externalSign_mul_componentShuffleIntegrand_eq_dysonFixedTimeAmplitude_permuted
    ε β g τ τ' shuffle σ]
  rw [d.1.ambientToTwoPointSlotTimePermutation_comp_ambientPermutation shuffle σ]

end Fermionic
end SecondQuantization
