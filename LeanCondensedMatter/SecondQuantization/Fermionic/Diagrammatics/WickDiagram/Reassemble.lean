import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Reassemble
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentConnected

set_option linter.style.header false

/-!
# Fermionic quartic diagram reassembly

This module specializes the label-generic quartic-diagram reassembly construction to fermionic
quartic vertex labels while preserving the existing public API.
-/

namespace SecondQuantization

variable {Mode : Type*} {N : ℕ}

noncomputable section

/-- The ambient flattened legs, identified with the disjoint union of each partition block's legs. -/
noncomputable def QuarticWickDiagram.bigLegEquiv {S : Finset (Fin N)} (π : Finpartition S) :
    Fin (2 * (2 * S.card)) ≃ Σ B : π.parts, Fin (2 * (2 * (B : Finset (Fin N)).card)) :=
  Common.QuarticDiagram.bigLegEquiv π

/-- `bigLegEquiv` at a leg constructed from an ambient vertex and a local leg. -/
theorem QuarticWickDiagram.bigLegEquiv_legOfVertexLocal {S : Finset (Fin N)}
    (π : Finpartition S) (v : ↥S) (i : Fin 4) :
    QuarticWickDiagram.bigLegEquiv π (legOfVertexLocal v i) =
      ⟨(π.equivSigmaParts v).1, legOfVertexLocal (π.equivSigmaParts v).2 i⟩ := by
  simpa only [QuarticWickDiagram.bigLegEquiv] using
    (Common.QuarticDiagram.bigLegEquiv_legOfVertexLocal π v i)

/-- The inverse of `bigLegEquiv` at a leg belonging to one partition block. -/
theorem QuarticWickDiagram.bigLegEquiv_symm_sigma_mk {S : Finset (Fin N)}
    (π : Finpartition S) (B : π.parts)
    (leg' : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    (QuarticWickDiagram.bigLegEquiv π).symm ⟨B, leg'⟩ =
      legOfVertexLocal (π.equivSigmaParts.symm ⟨B, vertexOfLeg leg'⟩) (localLegOfLeg leg') := by
  simpa only [QuarticWickDiagram.bigLegEquiv] using
    (Common.QuarticDiagram.bigLegEquiv_symm_sigma_mk π B leg')

/-- The pairing on the ambient legs obtained by gluing the pairings of all partition blocks. -/
noncomputable def QuarticWickDiagram.reassemblePairing {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N))) :
    Common.BlochDeDominicis.Pairing (2 * S.card) :=
  Common.QuarticDiagram.reassemblePairing π F

/-- Reassemble a fermionic quartic diagram from connected diagrams on partition blocks. -/
noncomputable def QuarticWickDiagram.reassemble {S : Finset (Fin N)} (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N))) :
    QuarticWickDiagram Mode N S :=
  Common.QuarticDiagram.reassemble π F

end

end SecondQuantization
