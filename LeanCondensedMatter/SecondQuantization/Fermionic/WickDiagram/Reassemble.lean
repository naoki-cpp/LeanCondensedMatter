import LeanCondensedMatter.SecondQuantization.Fermionic.WickDiagram.ComponentConnected

set_option linter.style.header false

/-!
# Reassembling a quartic Wick diagram from a partition and connected pieces

Given a `Finpartition S` and a connected quartic Wick diagram on each block,
`QuarticWickDiagram.reassemble` glues the block diagrams into one diagram on `S`.

The construction uses `QuarticWickDiagram.bigLegEquiv` to identify the ambient legs with the
disjoint union of the block legs. The pairing is assembled blockwise through
`Equiv.sigmaCongrRight` and transported back along this equivalence.
-/

namespace SecondQuantization

variable {Mode : Type*} {N : ℕ}

/-- **`S`'s flattened legs, identified with the disjoint union of each block's own legs**, via
`Finpartition.equivSigmaParts` (vertex level) and `quarticLegEquiv` (local-leg level) on both
sides. -/
noncomputable def QuarticWickDiagram.bigLegEquiv {S : Finset (Fin N)} (π : Finpartition S) :
    Fin (2 * (2 * S.card)) ≃ Σ B : π.parts, Fin (2 * (2 * (B : Finset (Fin N)).card)) :=
  (quarticLegEquiv S).trans <|
    (π.equivSigmaParts.prodCongr (Equiv.refl (Fin 4))).trans <|
      (Equiv.sigmaProdDistrib _ _).trans
        (Equiv.sigmaCongrRight fun B => (quarticLegEquiv (B : Finset (Fin N))).symm)

/-- `bigLegEquiv` at a leg constructed from an ambient vertex and a local leg. -/
theorem QuarticWickDiagram.bigLegEquiv_legOfVertexLocal {S : Finset (Fin N)}
    (π : Finpartition S) (v : ↥S) (i : Fin 4) :
    QuarticWickDiagram.bigLegEquiv π (legOfVertexLocal v i) =
      ⟨(π.equivSigmaParts v).1, legOfVertexLocal (π.equivSigmaParts v).2 i⟩ := by
  have hqv : quarticLegEquiv S (legOfVertexLocal v i) = (v, i) :=
    Equiv.apply_symm_apply (quarticLegEquiv S) (v, i)
  simp only [QuarticWickDiagram.bigLegEquiv, Equiv.trans_apply, hqv, Equiv.prodCongr_apply,
    Equiv.sigmaProdDistrib_apply, Equiv.sigmaCongrRight_apply]
  rfl

/-- The inverse of `bigLegEquiv` at a leg in one partition block. -/
theorem QuarticWickDiagram.bigLegEquiv_symm_sigma_mk {S : Finset (Fin N)}
    (π : Finpartition S) (B : π.parts)
    (leg' : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    (QuarticWickDiagram.bigLegEquiv π).symm ⟨B, leg'⟩ =
      legOfVertexLocal (π.equivSigmaParts.symm ⟨B, vertexOfLeg leg'⟩) (localLegOfLeg leg') := by
  have hqv : quarticLegEquiv (B : Finset (Fin N)) leg' =
      (vertexOfLeg leg', localLegOfLeg leg') := rfl
  simp only [QuarticWickDiagram.bigLegEquiv, Equiv.symm_trans_apply,
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

private theorem permCongr_involutive {α β : Type*} (e : α ≃ β) (p : Equiv.Perm α)
    (hp : Function.Involutive p) : Function.Involutive (e.permCongr p) := by
  intro x
  simp [Equiv.permCongr_apply, hp (e.symm x)]

private theorem permCongr_ne_self {α β : Type*} (e : α ≃ β) (p : Equiv.Perm α)
    (hp : ∀ x, p x ≠ x) (x : β) : e.permCongr p x ≠ x := by
  intro h
  rw [Equiv.permCongr_apply, Equiv.apply_eq_iff_eq_symm_apply] at h
  exact hp _ h

/-- **The reassembled pairing**, on `S`'s `4 * S.card` legs, glued from each block's own pairing
via `QuarticWickDiagram.bigLegEquiv`. -/
noncomputable def QuarticWickDiagram.reassemblePairing {S : Finset (Fin N)} (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N))) :
    Common.BlochDeDominicis.Pairing (2 * S.card) :=
  Common.BlochDeDominicis.Pairing.ofPartner
    ((QuarticWickDiagram.bigLegEquiv π).symm.permCongr
      (Equiv.sigmaCongrRight fun B => (F B).1.pairing.partner))
    ⟨permCongr_involutive _ _
        (sigmaCongrRight_involutive _ fun B => (F B).1.pairing.partner_involutive),
      permCongr_ne_self _ _
        (sigmaCongrRight_ne_self _ fun B => (F B).1.pairing.partner_ne_self)⟩

/-- **Reassembles a `QuarticWickDiagram Mode N S`** from an arbitrary `Finpartition S` and a
connected diagram on each block: each vertex's label is read off from its own block's diagram
(via `Finpartition.equivSigmaParts`), and the pairing is `QuarticWickDiagram.reassemblePairing`. -/
noncomputable def QuarticWickDiagram.reassemble {S : Finset (Fin N)} (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N))) :
    QuarticWickDiagram Mode N S where
  vertexLabel v := (F (π.equivSigmaParts v).1).1.vertexLabel (π.equivSigmaParts v).2
  pairing := QuarticWickDiagram.reassemblePairing π F

end SecondQuantization
