import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.CanonicalComponentShuffle

set_option linter.style.header false

/-!
# Ambient permutations underlying two-point component shuffles

Every interaction-component shuffle has the same dependent family of component-local slots as the
canonical shuffle.  Their difference is therefore an ambient permutation of interaction slots.
This module packages that permutation and records how arbitrary shuffled local-time restrictions
and shuffled products are obtained from the canonical ones by precomposing the ambient time
assignment with it.

This is the combinatorial coordinate bridge needed before identifying non-canonical shuffle terms
with interaction-vertex relabelings of fixed fermionic diagrams.
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
  d.canonicalComponentInteractionShuffle.slotEquiv.symm.trans shuffle.slotEquiv

/-- Applying the ambient permutation after the canonical slot equivalence recovers the chosen
component shuffle. -/
theorem TwoPointDiagram.ComponentInteractionShuffle.canonical_slotEquiv_trans_ambientPermutation
    {S : Finset (Fin N)} {d : TwoPointDiagram ExternalLabel InternalLabel N S}
    (shuffle : d.ComponentInteractionShuffle) :
    d.canonicalComponentInteractionShuffle.slotEquiv.trans shuffle.ambientPermutation =
      shuffle.slotEquiv := by
  ext x
  simp [TwoPointDiagram.ComponentInteractionShuffle.ambientPermutation]

/-- Pointwise form of `canonical_slotEquiv_trans_ambientPermutation`. -/
@[simp]
theorem TwoPointDiagram.ComponentInteractionShuffle.ambientPermutation_canonical_slotEquiv
    {S : Finset (Fin N)} {d : TwoPointDiagram ExternalLabel InternalLabel N S}
    (shuffle : d.ComponentInteractionShuffle)
    (x : Σ B : d.componentPartition.parts, Fin (d.interactionComponentSize B)) :
    shuffle.ambientPermutation
        (d.canonicalComponentInteractionShuffle.slotEquiv x) =
      shuffle.slotEquiv x := by
  simp [TwoPointDiagram.ComponentInteractionShuffle.ambientPermutation]

/-- The canonical component shuffle has the identity ambient permutation. -/
@[simp]
theorem TwoPointDiagram.canonicalComponentInteractionShuffle_ambientPermutation
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    d.canonicalComponentInteractionShuffle.ambientPermutation = Equiv.refl (Fin S.card) := by
  ext x
  simp [TwoPointDiagram.ComponentInteractionShuffle.ambientPermutation]

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
    τ (shuffle.ambientPermutation
      (d.canonicalComponentInteractionShuffle.slotEquiv ⟨B, i⟩))
  rw [shuffle.ambientPermutation_canonical_slotEquiv]

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

end

end Common
end SecondQuantization
