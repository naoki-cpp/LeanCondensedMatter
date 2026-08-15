import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.CanonicalComponentShuffle
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.InteractionVertexRelabel

set_option linter.style.header false

/-!
# Ambient permutations underlying two-point component shuffles

The relative ambient permutation between two family shuffles is owned by
`Combinatorics/FamilySlotShuffle.lean`. This module specializes that construction from the canonical
two-point component shuffle to a chosen component interaction shuffle, then records the resulting
time-coordinate and interaction-vertex transports.

For standard two-point diagrams on `Fin n`, it also transports the ambient permutation and time
coordinates between `Fin univ.card` and the explicit interaction-slot type `Fin n`, and packages the
corresponding interaction-vertex relabeling. These are diagram-specific coordinate adapters; the
underlying relative permutation is pure finite combinatorics.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

noncomputable section

/-- The ambient interaction-slot permutation carrying the canonical component interleaving to a
chosen component interaction shuffle. -/
def TwoPointDiagram.ComponentInteractionShuffle.ambientPermutation
    {S : Finset (Fin N)} {d : TwoPointDiagram ExternalLabel InternalLabel N S}
    (shuffle : d.ComponentInteractionShuffle) : Equiv.Perm (Fin S.card) :=
  d.canonicalComponentInteractionShuffle.relativeAmbientPermutation shuffle

/-- Restricting times along an arbitrary component shuffle is the same as first permuting the
ambient interaction-time coordinates and then using the canonical component restriction. -/
theorem TwoPointDiagram.ComponentInteractionShuffle.interactionComponentTimeAssignment_eq_canonical
    {S : Finset (Fin N)} {d : TwoPointDiagram ExternalLabel InternalLabel N S}
    (shuffle : d.ComponentInteractionShuffle)
    (τ : Fin S.card → ℝ) (B : d.componentPartition.parts) :
    d.interactionComponentTimeAssignment shuffle τ B =
      d.interactionComponentTimeAssignment d.canonicalComponentInteractionShuffle
        (fun i => τ (shuffle.ambientPermutation i)) B := by
  funext i
  change τ (shuffle.slotEquiv ⟨B, i⟩) =
    τ (d.canonicalComponentInteractionShuffle.relativeAmbientPermutation shuffle
      (d.canonicalComponentInteractionShuffle.slotEquiv ⟨B, i⟩))
  rw [Combinatorics.FamilySlotShuffleTo.relativeAmbientPermutation_slotEquiv]

/-- An arbitrary component-shuffle product is the canonical component-shuffle product evaluated on
the correspondingly permuted ambient interaction-time assignment. -/
theorem TwoPointDiagram.ComponentInteractionShuffle.interactionComponentShuffleIntegrand_eq_canonical
    {S : Finset (Fin N)} {d : TwoPointDiagram ExternalLabel InternalLabel N S}
    (shuffle : d.ComponentInteractionShuffle)
    (componentIntegrand :
      ∀ B : d.componentPartition.parts,
        (Fin (d.interactionComponentSize B) → ℝ) → ℂ)
    (τ : Fin S.card → ℝ) :
    d.interactionComponentShuffleIntegrand shuffle componentIntegrand τ =
      d.interactionComponentShuffleIntegrand d.canonicalComponentInteractionShuffle
        componentIntegrand (fun i => τ (shuffle.ambientPermutation i)) := by
  unfold TwoPointDiagram.interactionComponentShuffleIntegrand
  apply Fintype.prod_congr
  intro B
  rw [shuffle.interactionComponentTimeAssignment_eq_canonical τ B]

/-- Convert an ambient time assignment indexed by `univ.card` to the explicit interaction-slot type
`Fin n`. -/
def ambientToTwoPointSlotTimePermutation {n : ℕ}
    (σ : Fin (Finset.univ : Finset (Fin n)).card → ℝ) : Fin n → ℝ :=
  fun i => σ (Fin.cast (by simp) i)

/-- Convert an explicit `Fin n` time assignment back to the canonically equal ambient
`Fin univ.card` slot type. -/
def twoPointSlotToAmbientTimePermutation {n : ℕ}
    (σ : Fin n → ℝ) : Fin (Finset.univ : Finset (Fin n)).card → ℝ :=
  fun i => σ (Fin.cast (by simp) i)

@[simp]
theorem ambientToTwoPointSlotTimePermutation_twoPointSlotToAmbientTimePermutation
    {n : ℕ} (σ : Fin n → ℝ) :
    ambientToTwoPointSlotTimePermutation (twoPointSlotToAmbientTimePermutation σ) = σ := by
  funext i
  simp [ambientToTwoPointSlotTimePermutation, twoPointSlotToAmbientTimePermutation]

@[simp]
theorem twoPointSlotToAmbientTimePermutation_ambientToTwoPointSlotTimePermutation
    {n : ℕ} (σ : Fin (Finset.univ : Finset (Fin n)).card → ℝ) :
    twoPointSlotToAmbientTimePermutation (ambientToTwoPointSlotTimePermutation σ) = σ := by
  funext i
  simp [ambientToTwoPointSlotTimePermutation, twoPointSlotToAmbientTimePermutation]

/-- The canonical ambient-to-explicit time-coordinate conversion is continuous. -/
theorem continuous_ambientToTwoPointSlotTimePermutation {n : ℕ} :
    Continuous (fun σ : Fin (Finset.univ : Finset (Fin n)).card → ℝ =>
      ambientToTwoPointSlotTimePermutation σ) := by
  exact continuous_pi fun i => continuous_apply (Fin.cast (by simp) i)

/-- Injectivity is preserved when the ambient `Fin univ.card` time assignment is viewed on the
explicit standard slot type `Fin n`. -/
theorem ambientToTwoPointSlotTimePermutation_injective {n : ℕ}
    {σ : Fin (Finset.univ : Finset (Fin n)).card → ℝ}
    (hσ : Function.Injective σ) :
    Function.Injective (ambientToTwoPointSlotTimePermutation σ) := by
  intro a b hab
  apply Fin.ext
  have hcast := hσ hab
  exact congrArg (fun x : Fin (Finset.univ : Finset (Fin n)).card => x.val) hcast

/-- The component-shuffle ambient permutation transported from `Fin univ.card` to the explicit
interaction-slot type `Fin n` of a standard two-point diagram. -/
noncomputable def TwoPointDiagram.componentShuffleSlotPermutation
    {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (shuffle : d.ComponentInteractionShuffle) : Equiv.Perm (Fin n) :=
  (finCongr (by simp)).trans
    (shuffle.ambientPermutation.trans (finCongr (by simp)).symm)

/-- Transporting the ambient shuffle action to explicit interaction slots gives exactly
precomposition by `componentShuffleSlotPermutation`. -/
theorem TwoPointDiagram.ambientToTwoPointSlotTimePermutation_comp_ambientPermutation
    {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (shuffle : d.ComponentInteractionShuffle)
    (σ : Fin (Finset.univ : Finset (Fin n)).card → ℝ) :
    ambientToTwoPointSlotTimePermutation
        (fun k => σ (shuffle.ambientPermutation k)) =
      fun v => ambientToTwoPointSlotTimePermutation σ
        (d.componentShuffleSlotPermutation shuffle v) := by
  funext v
  simp [ambientToTwoPointSlotTimePermutation,
    TwoPointDiagram.componentShuffleSlotPermutation]
  rfl

/-- Relabel a standard two-point diagram by the inverse explicit-slot permutation associated with a
component shuffle. The inverse matches the convention that `relabelInteractionVertices` maps a new
slot to the old slot whose data it inherits. -/
noncomputable def TwoPointDiagram.relabelForComponentShuffle
    {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (shuffle : d.ComponentInteractionShuffle) :
    TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)) :=
  d.relabelInteractionVertices (d.componentShuffleSlotPermutation shuffle).symm

@[simp]
theorem TwoPointDiagram.relabelForComponentShuffle_externalLabel
    {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (shuffle : d.ComponentInteractionShuffle) :
    (d.relabelForComponentShuffle shuffle).externalLabel = d.externalLabel :=
  d.relabelInteractionVertices_externalLabel _

@[simp]
theorem TwoPointDiagram.relabelForComponentShuffle_vertexLabel
    {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (shuffle : d.ComponentInteractionShuffle) (v : Fin n) :
    (d.relabelForComponentShuffle shuffle).vertexLabel ⟨v, Finset.mem_univ _⟩ =
      d.vertexLabel ⟨(d.componentShuffleSlotPermutation shuffle).symm v, Finset.mem_univ _⟩ :=
  rfl

end

end Common
end SecondQuantization
