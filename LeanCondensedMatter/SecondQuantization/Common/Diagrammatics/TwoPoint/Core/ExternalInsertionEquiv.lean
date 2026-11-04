import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Core.Diagram
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Core.Diagram
import LeanCondensedMatter.Combinatorics.PerfectPairing.Transport

set_option linter.style.header false

/-!
# The two-point diagram as an external-insertion diagram with one external pair

The two diagram structures have identical external and interaction data at `E = 1`, but
their flattened leg enumerations are not definitionally the same.  The equivalence below
transports pairings along their explicit coordinate change instead of assuming that the
two enumerations agree or changing the existing two-point enumeration.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

/-- Change from the established two-point leg coordinates to the general external-insertion
coordinates at `E = 1`.  This is not assumed to preserve the numerical order of legs. -/
noncomputable def twoPointExternalInsertionLegEquiv (S : Finset (Fin N)) :
    Fin (2 * (2 * S.card + 1)) ≃ Fin (2 * (2 * S.card + 1)) :=
  (twoPointLegEquiv S).trans (externalInsertionLegEquiv 1 S).symm

@[simp]
theorem twoPointExternalInsertionLegEquiv_external (S : Finset (Fin N)) (e : Fin 2) :
    twoPointExternalInsertionLegEquiv S ((twoPointLegEquiv S).symm (Sum.inl e)) =
      (externalInsertionLegEquiv 1 S).symm (Sum.inl e) := by
  simp [twoPointExternalInsertionLegEquiv]

@[simp]
theorem twoPointExternalInsertionLegEquiv_interaction (S : Finset (Fin N))
    (v : ↥S) (l : Fin 4) :
    twoPointExternalInsertionLegEquiv S ((twoPointLegEquiv S).symm (Sum.inr (v, l))) =
      (externalInsertionLegEquiv 1 S).symm (Sum.inr (v, l)) := by
  simp [twoPointExternalInsertionLegEquiv]

/-- Identify two-point diagrams with the `E = 1` instance of general external-insertion
diagrams. Pairings are conjugated by the change of flattened leg coordinates. -/
noncomputable def TwoPointDiagram.externalInsertionEquiv (S : Finset (Fin N)) :
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
    refine TwoPointDiagram.ext rfl rfl ?_
    exact PairingOn.transport_transport_symm d.pairing
      (twoPointExternalInsertionLegEquiv S)
  right_inv d := by
    refine ExternalInsertionDiagram.ext rfl rfl ?_
    exact PairingOn.transport_symm_transport d.pairing
      (twoPointExternalInsertionLegEquiv S)

end Common
end SecondQuantization
