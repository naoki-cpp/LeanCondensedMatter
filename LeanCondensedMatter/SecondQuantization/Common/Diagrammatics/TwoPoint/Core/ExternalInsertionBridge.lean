import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Core.Diagram
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Core.Diagram

set_option linter.style.header false

/-!
# Two-point / arbitrary-external diagram data bridge

The established two-point diagrams and the `E = 1` arbitrary-external diagrams
carry the same labels and quartic vertices, but use independently chosen flattened
leg enumerations. Therefore their stored `Pairing` values must be transported;
reusing the same numeric pairing without reindexing is not valid.

This statistics-independent bridge leaves the mature two-point representation
unchanged. It does not identify the mixed-time fermionic signs, contractions,
Dyson integrals, or the resulting power series.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

/-- Match the independently chosen two-point and arbitrary-external flattened
leg coordinates by their common semantic external/interaction leg identities. -/
noncomputable def twoPointExternalInsertionLegEquiv (S : Finset (Fin N)) :
    Fin (2 * (2 * S.card + 1)) ≃ Fin (2 * (2 * S.card + 1)) :=
  (twoPointLegEquiv S).trans (externalInsertionLegEquiv 1 S).symm

/-- The coordinate change does not change the incident vertex of a leg. -/
theorem twoPointExternalInsertionLegEquiv_vertexOfLeg (S : Finset (Fin N))
    (p : Fin (2 * (2 * S.card + 1))) :
    externalInsertionVertexOfLeg (E := 1) (twoPointExternalInsertionLegEquiv S p) =
      twoPointVertexOfLeg p := by
  simp only [externalInsertionVertexOfLeg, twoPointVertexOfLeg,
    twoPointExternalInsertionLegEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  cases h : twoPointLegEquiv S p with
  | inl e => simp
  | inr v => simp

/-- Exactly the same labelled-and-paired combinatorial data, with its pairing
transported between the two flattened-leg conventions. -/
noncomputable def twoPointDiagramExternalInsertionEquiv (S : Finset (Fin N)) :
    TwoPointDiagram ExternalLabel InternalLabel N S ≃
      ExternalInsertionDiagram ExternalLabel InternalLabel 1 N S where
  toFun d :=
    { externalLabel := d.externalLabel
      vertexLabel := d.vertexLabel
      pairing := d.pairing.transport (twoPointExternalInsertionLegEquiv S).symm }
  invFun d :=
    { externalLabel := d.externalLabel
      vertexLabel := d.vertexLabel
      pairing := d.pairing.transport (twoPointExternalInsertionLegEquiv S) }
  left_inv d := by
    apply TwoPointDiagram.ext
    · rfl
    · rfl
    · exact PairingOn.transport_transport_symm d.pairing
        (twoPointExternalInsertionLegEquiv S)
  right_inv d := by
    apply ExternalInsertionDiagram.ext
    · rfl
    · rfl
    · exact PairingOn.transport_symm_transport d.pairing
        (twoPointExternalInsertionLegEquiv S)

/-- Transported pairing partners correspond on the same semantic leg. -/
theorem twoPointDiagramExternalInsertionEquiv_partner (S : Finset (Fin N))
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (p : Fin (2 * (2 * S.card + 1))) :
    (twoPointDiagramExternalInsertionEquiv S d).pairing.partner
        (twoPointExternalInsertionLegEquiv S p) =
      twoPointExternalInsertionLegEquiv S (d.pairing.partner p) := by
  simp [twoPointDiagramExternalInsertionEquiv, PairingOn.transport_partner]

/-- The graph of paired vertices is preserved. The isomorphism fixes each
external and interaction vertex, rather than arbitrarily relabelling them. -/
noncomputable def TwoPointDiagram.externalInsertionGraphIso
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    d.vertexGraph ≃g (twoPointDiagramExternalInsertionEquiv S d).vertexGraph :=
  d.pairing.vertexGraphTransportIso (twoPointExternalInsertionLegEquiv S)
    (twoPointVertexOfLeg (S := S))
    (externalInsertionVertexOfLeg (E := 1) (S := S))
    (Equiv.refl _) (twoPointExternalInsertionLegEquiv_vertexOfLeg S)

end Common
end SecondQuantization
