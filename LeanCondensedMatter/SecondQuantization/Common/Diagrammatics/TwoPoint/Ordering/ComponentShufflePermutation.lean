import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Ordering.CanonicalComponentShuffle
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Ordering.InteractionVertexRelabel

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
  apply congrArg (componentIntegrand B)
  funext i
  change τ (shuffle.slotEquiv ⟨B, i⟩) =
    τ (d.canonicalComponentInteractionShuffle.relativeAmbientPermutation shuffle
      (d.canonicalComponentInteractionShuffle.slotEquiv ⟨B, i⟩))
  rw [Combinatorics.FamilySlotShuffleTo.relativeAmbientPermutation_slotEquiv]

/-- Canonical identification of explicit two-point interaction slots with the ambient `univ.card`
slot coordinates. -/
noncomputable def twoPointSlotEquiv {n : ℕ} :
    Fin n ≃ Fin (Finset.univ : Finset (Fin n)).card :=
  finCongr (by simp)

/-- Canonical equivalence between ambient and explicit two-point interaction-time assignments. -/
noncomputable def twoPointSlotTimeEquiv {n : ℕ} :
    (Fin (Finset.univ : Finset (Fin n)).card → ℝ) ≃ (Fin n → ℝ) where
  toFun σ i := σ (Fin.cast (by simp) i)
  invFun σ i := σ (Fin.cast (by simp) i)
  left_inv σ := by
    funext i
    simp
  right_inv σ := by
    funext i
    simp

/-- The component-shuffle ambient permutation transported from `Fin univ.card` to the explicit
interaction-slot type `Fin n` of a standard two-point diagram. -/
noncomputable def TwoPointDiagram.componentShuffleSlotPermutation
    {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (shuffle : d.ComponentInteractionShuffle) : Equiv.Perm (Fin n) :=
  twoPointSlotEquiv.trans
    (shuffle.ambientPermutation.trans twoPointSlotEquiv.symm)

/-- Transporting the ambient shuffle action to explicit interaction slots gives exactly
precomposition by `componentShuffleSlotPermutation`. -/
theorem TwoPointDiagram.twoPointSlotTimeEquiv_comp_ambientPermutation
    {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (shuffle : d.ComponentInteractionShuffle)
    (σ : Fin (Finset.univ : Finset (Fin n)).card → ℝ) :
    twoPointSlotTimeEquiv (fun k => σ (shuffle.ambientPermutation k)) =
      fun v => twoPointSlotTimeEquiv σ
        (d.componentShuffleSlotPermutation shuffle v) := by
  funext v
  simp [twoPointSlotTimeEquiv, twoPointSlotEquiv,
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
