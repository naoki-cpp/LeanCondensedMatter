import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.ExternalPiece
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedPairContractionRegularity

set_option linter.style.header false

/-!
# The external piece carries the same fields as the ambient diagram

A leg of the external piece and the ambient leg it is sent to by the slot reindexing describe the
same physical field: the external legs are literally the same, and an interaction leg keeps its
local coordinate while its slot's label and time are, by construction, the ones the piece inherits.

So the mixed field and operator families agree along the embedding of mixed positions, and with them
the free Gibbs contraction of any two positions. That is the value half of the linked-cluster step:
the external component's contractions may be computed in the piece, at the times it inherits.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {n : ℕ} {i j : Mode}

omit [LinearOrder Mode] [Fintype Mode] in
/-- **A leg of the piece describes the same field as the ambient leg it is sent to.** -/
theorem FixedExternalTwoPointWickDiagram.orderedTwoPointLegField_orderedTwoPointLegMap
    (d : FixedExternalTwoPointWickDiagram Mode n i j) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (leg : OrderedTwoPointLeg d.1.externalInteractionPart.card) :
    orderedTwoPointLegField i j τ τ' d.vertexLabelSequence σ
        (orderedTwoPointLegMap (d.1.externalInteractionPart.orderEmbOfFin rfl) leg) =
      orderedTwoPointLegField i j τ τ' d.externalPiece.vertexLabelSequence
        (d.externalPieceTimes σ) leg := by
  cases leg with
  | inl e => rfl
  | inr p =>
      obtain ⟨v, l⟩ := p
      simp only [orderedTwoPointLegMap_inr, orderedTwoPointLegField,
        orderedTwoPointLegTime, orderedTwoPointLegFieldLabel]
      rw [d.externalPiece_vertexLabelSequence]
      rfl

omit [Fintype Mode] in
/-- The mixed field family of the ambient diagram, read at a position of the piece, is the piece's
own mixed field family. -/
theorem FixedExternalTwoPointWickDiagram.mixedTimeOrderedAtomicFieldFamily_externalPieceMixedPosition
    (d : FixedExternalTwoPointWickDiagram Mode n i j) (ε : Mode → ℝ) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (p : Fin (2 * (2 * d.1.externalInteractionPart.card + 1))) :
    mixedTimeOrderedAtomicFieldFamily ε i j τ τ' d.vertexLabelSequence σ
        (d.externalPieceMixedPosition τ τ' σ p) =
      mixedTimeOrderedAtomicFieldFamily ε i j τ τ' d.externalPiece.vertexLabelSequence
        (d.externalPieceTimes σ) p := by
  rw [mixedTimeOrderedAtomicFieldFamily_eq_orderedTwoPointLegField,
    mixedTimeOrderedAtomicFieldFamily_eq_orderedTwoPointLegField,
    d.mixedTimeOrderedAtomicLegEquiv_externalPieceMixedPosition,
    d.orderedTwoPointLegField_orderedTwoPointLegMap]

omit [Fintype Mode] in
/-- Operator form: the piece's mixed operator family is the ambient one along the embedding. -/
theorem
    FixedExternalTwoPointWickDiagram.mixedTimeOrderedAtomicOperatorFamily_externalPieceMixedPosition
    (d : FixedExternalTwoPointWickDiagram Mode n i j) (ε : Mode → ℝ) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (p : Fin (2 * (2 * d.1.externalInteractionPart.card + 1))) :
    mixedTimeOrderedAtomicOperatorFamily ε i j τ τ' d.vertexLabelSequence σ
        (d.externalPieceMixedPosition τ τ' σ p) =
      mixedTimeOrderedAtomicOperatorFamily ε i j τ τ' d.externalPiece.vertexLabelSequence
        (d.externalPieceTimes σ) p := by
  change timedFieldOperator ε
      (mixedTimeOrderedAtomicFieldFamily ε i j τ τ' d.vertexLabelSequence σ
        (d.externalPieceMixedPosition τ τ' σ p)) = _
  rw [d.mixedTimeOrderedAtomicFieldFamily_externalPieceMixedPosition]
  rfl

/-- **The external component's contractions are the piece's contractions.** The free Gibbs
contraction of two ambient positions coming from the piece is the piece's own contraction of those
positions, evaluated at the times it inherits. -/
theorem FixedExternalTwoPointWickDiagram.mixedTimeOrderedAtomicPairValue_externalPieceMixedPosition
    (d : FixedExternalTwoPointWickDiagram Mode n i j) (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ)
    (σ : Fin n → ℝ) (a b : Fin (2 * (2 * d.1.externalInteractionPart.card + 1))) :
    mixedTimeOrderedAtomicPairValue ε β i j τ τ' σ d.vertexLabelSequence
        (d.externalPieceMixedPosition τ τ' σ a) (d.externalPieceMixedPosition τ τ' σ b) =
      mixedTimeOrderedAtomicPairValue ε β i j τ τ' (d.externalPieceTimes σ)
        d.externalPiece.vertexLabelSequence a b := by
  rw [mixedTimeOrderedAtomicPairValue, mixedTimeOrderedAtomicPairValue,
    d.mixedTimeOrderedAtomicOperatorFamily_externalPieceMixedPosition,
    d.mixedTimeOrderedAtomicOperatorFamily_externalPieceMixedPosition]

end Fermionic
end SecondQuantization
