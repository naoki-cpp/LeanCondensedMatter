import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentShufflePermutation
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentCanonicalLocality
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.InteractionVertexRelabel

set_option linter.style.header false

/-!
# Component-shuffle permutations for fixed fermionic two-point diagrams

The Common layer shows that every component interaction shuffle differs from the canonical shuffle
by an ambient interaction-slot permutation.  For a fixed fermionic diagram, the canonical shuffled
product is exactly the pointwise Dyson amplitude up to the external ordering sign.  Combining these
facts identifies every non-canonical shuffled product with the canonical component-local product
evaluated on permuted interaction-time coordinates.

The ambient permutation naturally acts on `Fin univ.card`, while a fixed fermionic diagram uses the
explicit slot type `Fin n`.  This file also transports that permutation to `Fin n` and records the
interaction-vertex relabeling with the inverse permutation.  The inverse is forced by the convention
of `relabelInteractionVertices`: its permutation maps a new slot to the old slot whose data it
inherits, whereas the component-shuffle permutation acts by precomposition on the old diagram's
time assignment.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Convert an ambient time assignment indexed by `univ.card` to the explicit interaction-slot type
`Fin n`. -/
def ambientToTwoPointSlotTimePermutation {n : ℕ}
    (σ : Fin (Finset.univ : Finset (Fin n)).card → ℝ) : Fin n → ℝ :=
  fun i => σ (Fin.cast (by simp) i)

/-- The component-shuffle ambient permutation transported from `Fin univ.card` to the explicit
interaction-slot type `Fin n`. -/
noncomputable def FixedExternalTwoPointWickDiagram.componentShuffleSlotPermutation
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (shuffle : d.1.ComponentInteractionShuffle) : Equiv.Perm (Fin n) :=
  (finCongr (by simp)).trans
    (shuffle.ambientPermutation.trans (finCongr (by simp)).symm)

omit [LinearOrder Mode] [Fintype Mode] in
/-- Transporting the ambient shuffle action to explicit interaction slots gives exactly
precomposition by `componentShuffleSlotPermutation`. -/
theorem FixedExternalTwoPointWickDiagram.ambientToTwoPointSlotTimePermutation_comp_ambientPermutation
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (shuffle : d.1.ComponentInteractionShuffle)
    (σ : Fin (Finset.univ : Finset (Fin n)).card → ℝ) :
    ambientToTwoPointSlotTimePermutation
        (fun k => σ (shuffle.ambientPermutation k)) =
      fun v => ambientToTwoPointSlotTimePermutation σ
        (d.componentShuffleSlotPermutation shuffle v) := by
  funext v
  simp [ambientToTwoPointSlotTimePermutation,
    FixedExternalTwoPointWickDiagram.componentShuffleSlotPermutation]
  rfl

/-- The diagram relabeling corresponding to a component shuffle.  Because
`relabelInteractionVertices` maps new slots to the old slots whose data they inherit, the inverse of
the shuffle slot permutation is used here. -/
noncomputable def FixedExternalTwoPointWickDiagram.relabelForComponentShuffle
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (shuffle : d.1.ComponentInteractionShuffle) : FixedExternalTwoPointWickDiagram Mode n i j :=
  d.relabelInteractionVertices (d.componentShuffleSlotPermutation shuffle).symm

omit [LinearOrder Mode] [Fintype Mode] in
@[simp]
theorem FixedExternalTwoPointWickDiagram.relabelForComponentShuffle_vertexLabelSequence
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (shuffle : d.1.ComponentInteractionShuffle) (v : Fin n) :
    (d.relabelForComponentShuffle shuffle).vertexLabelSequence v =
      d.vertexLabelSequence ((d.componentShuffleSlotPermutation shuffle).symm v) :=
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
          (d.componentShuffleSlotPermutation shuffle v)) := by
  rw [d.externalSign_mul_componentShuffleIntegrand_eq_dysonFixedTimeAmplitude_permuted
    ε β g τ τ' shuffle σ]
  rw [d.ambientToTwoPointSlotTimePermutation_comp_ambientPermutation shuffle σ]

end Fermionic
end SecondQuantization
