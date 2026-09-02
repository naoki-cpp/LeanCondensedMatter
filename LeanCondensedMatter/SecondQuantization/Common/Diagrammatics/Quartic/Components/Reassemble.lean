import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Components.ComponentConnected

set_option linter.style.header false

/-!
# Reassembling a labelled quartic diagram from connected pieces

Given a partition of the ambient vertex set and a connected labelled quartic diagram on each part,
this module glues the block diagrams into one diagram. The construction depends only on quartic leg
indexing and pairings, not on the label type or particle statistics.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {Label : Type*} {N : ℕ}

/-- The ambient flattened legs, identified with the disjoint union of each partition part's legs. -/
noncomputable def QuarticDiagram.bigLegEquiv {S : Finset (Fin N)} (π : Finpartition S) :
    Fin (2 * (2 * S.card)) ≃ Σ B : π.parts, Fin (2 * (2 * (B : Finset (Fin N)).card)) :=
  (quarticLegEquiv S).trans <|
    (π.equivSigmaParts.prodCongr (Equiv.refl (Fin 4))).trans <|
      (Equiv.sigmaProdDistrib _ _).trans
        (Equiv.sigmaCongrRight fun B => (quarticLegEquiv (B : Finset (Fin N))).symm)

/-- `bigLegEquiv` at a leg constructed from an ambient vertex and a local leg. -/
theorem QuarticDiagram.bigLegEquiv_legOfVertexLocal {S : Finset (Fin N)}
    (π : Finpartition S) (v : ↥S) (i : Fin 4) :
    QuarticDiagram.bigLegEquiv π (legOfVertexLocal v i) =
      ⟨(π.equivSigmaParts v).1, legOfVertexLocal (π.equivSigmaParts v).2 i⟩ := by
  have hqv : quarticLegEquiv S (legOfVertexLocal v i) = (v, i) :=
    Equiv.apply_symm_apply (quarticLegEquiv S) (v, i)
  simp only [QuarticDiagram.bigLegEquiv, Equiv.trans_apply, hqv, Equiv.prodCongr_apply,
    Equiv.sigmaProdDistrib_apply, Equiv.sigmaCongrRight_apply]
  rfl

/-- The inverse of `bigLegEquiv` at a leg belonging to one partition part. -/
theorem QuarticDiagram.bigLegEquiv_symm_sigma_mk {S : Finset (Fin N)}
    (π : Finpartition S) (B : π.parts)
    (leg' : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    (QuarticDiagram.bigLegEquiv π).symm ⟨B, leg'⟩ =
      legOfVertexLocal (π.equivSigmaParts.symm ⟨B, vertexOfLeg leg'⟩) (localLegOfLeg leg') := by
  have hqv : quarticLegEquiv (B : Finset (Fin N)) leg' =
      (vertexOfLeg leg', localLegOfLeg leg') := rfl
  simp only [QuarticDiagram.bigLegEquiv, Equiv.symm_trans_apply,
    Equiv.sigmaCongrRight_symm, Equiv.sigmaCongrRight_apply, Equiv.symm_symm, hqv,
    Equiv.sigmaProdDistrib_symm_apply, Equiv.prodCongr_symm, Equiv.refl_symm]
  rfl

private theorem sigmaCongrRight_involutive {ι : Type*} {β : ι → Type*}
    (F : ∀ i, Equiv.Perm (β i)) (hF : ∀ i, Function.Involutive (F i)) :
    Function.Involutive (Equiv.sigmaCongrRight F) := by
  rintro ⟨i, x⟩
  simp [hF i x]

private theorem sigmaCongrRight_ne_self {ι : Type*} {β : ι → Type*}
    (F : ∀ i, Equiv.Perm (β i)) (hF : ∀ i x, F i x ≠ x) (p : Σ i, β i) :
    Equiv.sigmaCongrRight F p ≠ p := by
  obtain ⟨i, x⟩ := p
  simp only [Equiv.sigmaCongrRight_apply, ne_eq, Sigma.mk.injEq, heq_eq_eq, true_and]
  exact hF i x

/-- The pairing on the ambient legs obtained by gluing the pairings of all partition parts. -/
noncomputable def QuarticDiagram.reassemblePairing {S : Finset (Fin N)} (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticDiagram Label N (B : Finset (Fin N))) :
    Combinatorics.Pairing (2 * S.card) :=
  Combinatorics.Pairing.ofPartner
    ((QuarticDiagram.bigLegEquiv π).symm.permCongr
      (Equiv.sigmaCongrRight fun B => (F B).1.pairing.partner))
    (IsPairing.permCongr
      ⟨sigmaCongrRight_involutive _ fun B => (F B).1.pairing.partner_involutive,
        sigmaCongrRight_ne_self _ fun B => (F B).1.pairing.partner_ne⟩
      (QuarticDiagram.bigLegEquiv π).symm)

/-- Reassemble an ambient labelled quartic diagram from connected diagrams on partition parts. -/
noncomputable def QuarticDiagram.reassemble {S : Finset (Fin N)} (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticDiagram Label N (B : Finset (Fin N))) :
    QuarticDiagram Label N S where
  vertexLabel v := (F (π.equivSigmaParts v).1).1.vertexLabel (π.equivSigmaParts v).2
  pairing := QuarticDiagram.reassemblePairing π F

end Common
end SecondQuantization
