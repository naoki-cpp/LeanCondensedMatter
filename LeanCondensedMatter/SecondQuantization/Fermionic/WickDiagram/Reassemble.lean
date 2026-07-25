import LeanCondensedMatter.SecondQuantization.Fermionic.WickDiagram.ComponentConnected

set_option linter.style.header false

/-!
# Reassembling a quartic Wick diagram from a partition and connected pieces

The converse of `QuarticWickDiagram.restrictComponent`: given an arbitrary `Finpartition S` and a
connected quartic Wick diagram on each of its blocks, `QuarticWickDiagram.reassemble` glues them
into a single `QuarticWickDiagram Mode N S`. Unlike `restrictComponent` (which restricts an
*existing* diagram to one of its *own* component blocks), `reassemble` starts from no ambient
diagram at all — the partition and the per-block pieces are independent data.

The construction goes through `QuarticWickDiagram.bigLegEquiv`, identifying `S`'s `4 * S.card`
legs with the disjoint union (`Σ`-type) of each block's own legs, via
`Finpartition.equivSigmaParts`; the reassembled pairing is then a block-by-block gluing of each
piece's own `Pairing.partner` (`Equiv.sigmaCongrRight`), transported back along `bigLegEquiv`.

The full `QuarticWickDiagram Mode N S ≃ Σ π : Finpartition S, ∀ B : π.parts,
ConnectedQuarticWickDiagram Mode N B` equivalence `Combinatorics.WeightedDiagramFamily.decompose`
needs (i.e. that `reassemble` and `restrictComponent`/`componentPartition` are mutually inverse)
remains future work.
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
