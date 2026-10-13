import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.MixedOrderData
import LeanCondensedMatter.Combinatorics.FamilySlotShuffleSign
import LeanCondensedMatter.Combinatorics.SigmaPermutationSign

set_option linter.style.header false

/-!
# Relative fixed/mixed component shuffles

The relative permutation compares component-local fixed and mixed positions. Its integer-unit
permutation sign is the ambient mixed-order sign times the component-local signs. This is a
statistics-independent permutation identity; fermionic scalar sign semantics are downstream.
-/

namespace SecondQuantization
namespace Common

open Combinatorics
open scoped BigOperators

variable {ExternalLabel InternalLabel : Type*}

/-- Relative permutation from fixed component-local atomic positions to mixed-time component-local
atomic positions. -/
noncomputable def ExternalInsertionDiagram.relativeComponentShuffle
    {E n : ℕ}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E n
      (Finset.univ : Finset (Fin n)))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    Equiv.Perm (Fin (2 * (2 * n + E))) :=
  (FamilySlotShuffleTo.castTotalEquiv
      (m := 2 * (2 * (Finset.univ : Finset (Fin n)).card + E))
      (n := 2 * (2 * n + E)) (by simp) d.componentLegShuffle).relativePerm
    (d.componentMixedPositionShuffle externalTime σ)

/-- The relative component shuffle sign is the ambient mixed-time ordering sign times the product
of the component-local mixed-time ordering signs. This is the final permutation-sign bridge needed
to turn mixed-pairing factorization into a fixed-time amplitude factorization. -/
theorem ExternalInsertionDiagram.relativeComponentShuffle_sign_eq_mixedAtomic_mul_prod_components
    {E n : ℕ}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E n
      (Finset.univ : Finset (Fin n)))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    Equiv.Perm.sign (d.relativeComponentShuffle externalTime σ) =
      Equiv.Perm.sign
          (externalInsertionStandardToMixedAtomicPositionEquiv externalTime σ) *
        ∏ B : d.vertexGraph.componentPartition.parts,
          Equiv.Perm.sign
            (externalInsertionStandardToMixedAtomicPositionEquiv
              (d.componentExternalTime externalTime B)
              (d.componentInteractionTime σ B)) := by
  classical
  let fixedShuffle :=
    FamilySlotShuffleTo.castTotalEquiv
      (m := 2 * (2 * (Finset.univ : Finset (Fin n)).card + E))
      (n := 2 * (2 * n + E)) (by simp) d.componentLegShuffle
  let globalPerm :=
    externalInsertionStandardToMixedAtomicPositionEquiv externalTime σ
  let localPerm :
      ∀ B : d.vertexGraph.componentPartition.parts,
        Equiv.Perm
          (Fin (2 * (2 * (interactionSector
            (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).card +
              d.externalPairCount B))) :=
    fun B =>
      (externalInsertionMixedTimeAmbientPositionEquiv
        (d.componentExternalTime externalTime B)
        (d.componentInteractionTime σ B)).trans
        (finCongr (by simp))
  have hmixed :
      (d.componentMixedPositionShuffle externalTime σ).slotEquiv =
        (Equiv.sigmaCongrRight localPerm).trans
          (fixedShuffle.slotEquiv.trans globalPerm) := by
    apply Equiv.ext
    rintro ⟨B, p⟩
    apply Fin.ext
    rfl
  have hrelative :
      d.relativeComponentShuffle externalTime σ =
        ((fixedShuffle.slotEquiv.symm.trans
            (Equiv.sigmaCongrRight localPerm)).trans
          fixedShuffle.slotEquiv).trans globalPerm := by
    unfold ExternalInsertionDiagram.relativeComponentShuffle
      FamilySlotShuffleTo.relativePerm
    change fixedShuffle.slotEquiv.symm.trans
        (d.componentMixedPositionShuffle externalTime σ).slotEquiv = _
    rw [hmixed]
    apply Equiv.ext
    intro p
    rfl
  rw [hrelative, Equiv.Perm.sign_trans,
    Equiv.Perm.sign_symm_trans_trans,
    Equiv.Perm.sign_sigmaCongrRight]
  change Equiv.Perm.sign globalPerm *
      (∏ B : d.vertexGraph.componentPartition.parts,
        Equiv.Perm.sign (localPerm B)) =
    Equiv.Perm.sign globalPerm * _
  congr 1
  apply Finset.prod_congr rfl
  intro B _
  have hperm :
      localPerm B =
        (externalInsertionStandardToMixedAtomicPositionEquiv
          (d.componentExternalTime externalTime B)
          (d.componentInteractionTime σ B)).symm := by
    apply Equiv.ext
    intro p
    apply Fin.ext
    rfl
  rw [hperm, Equiv.Perm.sign_symm]


end Common
end SecondQuantization
