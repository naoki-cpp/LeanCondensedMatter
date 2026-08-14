import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentShufflePermutation
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.MixedComponentTimeTransport

set_option linter.style.header false

/-!
# Canonical component-local time transport

For standard two-point diagrams, equality of the local coordinates selected by the canonical
component shuffle implies the `ComponentTimeEq` relation used by mixed component transport. The
only coordinate conversion is the Common `Fin univ.card ↔ Fin n` cast.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*}

/-- Equality on the local coordinates of the canonical component shuffle is exactly sufficient for
the component-time equality used by mixed component transport. -/
theorem TwoPointDiagram.componentTimeEq_of_canonicalAssignment_eq
    {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (B : d.componentPartition.parts)
    (σ υ : Fin (Finset.univ : Finset (Fin n)).card → ℝ)
    (hσυ : DependentSlotEquiv.assignment
        d.canonicalComponentInteractionShuffle.slotEquiv σ B =
      DependentSlotEquiv.assignment
        d.canonicalComponentInteractionShuffle.slotEquiv υ B) :
    d.ComponentTimeEq B
      (ambientToTwoPointSlotTimePermutation σ)
      (ambientToTwoPointSlotTimePermutation υ) := by
  have hRestricted :
      d.interactionComponentTimeAssignment
          d.canonicalComponentInteractionShuffle σ B =
        d.interactionComponentTimeAssignment
          d.canonicalComponentInteractionShuffle υ B :=
    hσυ
  have hVertices :
      ∀ v : ↥(TwoPointDiagram.interactionPart
        (B : Finset (TwoPointVertex (Finset.univ : Finset (Fin n))))),
        ambientToTwoPointSlotTimePermutation σ v.1 =
          ambientToTwoPointSlotTimePermutation υ v.1 := by
    apply (d.canonicalComponentTimeAssignment_univ_eq_iff
      (ambientToTwoPointSlotTimePermutation σ)
      (ambientToTwoPointSlotTimePermutation υ) B).mp
    simpa [ambientToTwoPointSlotTimePermutation] using hRestricted
  intro v hv
  exact hVertices ⟨v, hv⟩

end Common
end SecondQuantization
