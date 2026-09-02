import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.External.ExternalConnectivity

set_option linter.style.header false

/-!
# Transporting a two-point diagram along a relabeling of its interaction vertices

A two-point diagram carries its interaction vertices as a `Finset`.  The pieces produced by the
external/vacuum split therefore live on subsets, while the perturbative coefficient at order `k`
ranges over diagrams whose vertex set is all of `Fin k`.  Moving between the two is a relabeling of
the interaction vertices along an equivalence of vertex types, and this module builds it.

The transport renames legs through the two leg enumerations, so it commutes with the incidence map
and hence induces an isomorphism of vertex graphs.  Every connectivity notion is therefore
preserved: reachability, absence of vacuum components, and external connectedness.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {N M : ℕ} {T : Finset (Fin N)} {U : Finset (Fin M)}

/-- The increasing enumeration of a finite slot set, viewed as a relabeling onto the standard full
slot set of the same cardinality. -/
noncomputable def standardSlotEquiv (T : Finset (Fin N)) :
    ↥T ≃ ↥(Finset.univ : Finset (Fin T.card)) :=
  (T.orderIsoOfFin rfl).toEquiv.symm.trans
    (Equiv.subtypeUnivEquiv (fun x : Fin T.card => Finset.mem_univ x)).symm

@[simp]
theorem standardSlotEquiv_symm_coe (T : Finset (Fin N))
    (v : ↥(Finset.univ : Finset (Fin T.card))) :
    (((standardSlotEquiv T).symm v : ↥T) : Fin N) =
      T.orderEmbOfFin rfl (v : Fin T.card) := by
  simp [standardSlotEquiv, Finset.coe_orderIsoOfFin_apply]

/-- Relabeling the interaction vertices relabels the two-point vertices. -/
def twoPointVertexCongr (e : ↥T ≃ ↥U) : TwoPointVertex T ≃ TwoPointVertex U :=
  Equiv.sumCongr (Equiv.refl (Fin 2)) e

@[simp]
theorem twoPointVertexCongr_inl (e : ↥T ≃ ↥U) (a : Fin 2) :
    twoPointVertexCongr e (Sum.inl a) = Sum.inl a := rfl

@[simp]
theorem twoPointVertexCongr_inr (e : ↥T ≃ ↥U) (v : ↥T) :
    twoPointVertexCongr e (Sum.inr v) = Sum.inr (e v) := rfl

/-- Relabeling the interaction vertices relabels the unflattened legs. -/
def twoPointLegDataCongr (e : ↥T ≃ ↥U) : TwoPointLeg T ≃ TwoPointLeg U :=
  Equiv.sumCongr (Equiv.refl (Fin 2)) (e.prodCongr (Equiv.refl (Fin 4)))

@[simp]
theorem twoPointLegDataCongr_inl (e : ↥T ≃ ↥U) (a : Fin 2) :
    twoPointLegDataCongr e (Sum.inl a) = Sum.inl a := rfl

@[simp]
theorem twoPointLegDataCongr_inr (e : ↥T ≃ ↥U) (v : ↥T) (l : Fin 4) :
    twoPointLegDataCongr e (Sum.inr (v, l)) = Sum.inr (e v, l) := rfl

/-- Relabeling the interaction vertices relabels the flattened legs. -/
noncomputable def twoPointLegCongr (e : ↥T ≃ ↥U) :
    Fin (2 * (2 * T.card + 1)) ≃ Fin (2 * (2 * U.card + 1)) :=
  (twoPointLegEquiv T).trans
    ((Equiv.sumCongr (Equiv.refl (Fin 2)) (e.prodCongr (Equiv.refl (Fin 4)))).trans
      (twoPointLegEquiv U).symm)

/-- The flattened relabeling is the unflattened one read through the two leg enumerations. -/
theorem twoPointLegCongr_eq_trans (e : ↥T ≃ ↥U) :
    twoPointLegCongr e =
      (twoPointLegEquiv T).trans ((twoPointLegDataCongr e).trans (twoPointLegEquiv U).symm) :=
  rfl

/-- The inverse relabeling of legs is the relabeling along the inverse. -/
theorem twoPointLegCongr_symm (e : ↥T ≃ ↥U) :
    twoPointLegCongr e.symm = (twoPointLegCongr e).symm := by
  refine Equiv.ext fun leg => ?_
  obtain ⟨x, rfl⟩ := (twoPointLegEquiv U).symm.surjective leg
  cases x with
  | inl a => simp [twoPointLegCongr]
  | inr p =>
      obtain ⟨v, l⟩ := p
      simp [twoPointLegCongr]

/-- The relabeled leg carries the relabeled vertex. -/
theorem twoPointVertexOfLeg_twoPointLegCongr (e : ↥T ≃ ↥U)
    (leg : Fin (2 * (2 * T.card + 1))) :
    twoPointVertexOfLeg (twoPointLegCongr e leg) =
      twoPointVertexCongr e (twoPointVertexOfLeg leg) := by
  obtain ⟨x, rfl⟩ := (twoPointLegEquiv T).symm.surjective leg
  cases x with
  | inl a => simp [twoPointLegCongr, twoPointVertexOfLeg, twoPointVertexCongr]
  | inr p =>
      obtain ⟨v, l⟩ := p
      simp [twoPointLegCongr, twoPointVertexOfLeg, twoPointVertexCongr]

/-- **Transport a two-point diagram along a relabeling of its interaction vertices.** -/
noncomputable def TwoPointDiagram.slotCongr (e : ↥T ≃ ↥U)
    (d : TwoPointDiagram ExternalLabel InternalLabel N T) :
    TwoPointDiagram ExternalLabel InternalLabel M U where
  externalLabel := d.externalLabel
  vertexLabel v := d.vertexLabel (e.symm v)
  pairing :=
    Pairing.ofPartner ((twoPointLegCongr e).permCongr d.pairing.partner)
      ⟨by
        intro i
        simp [Equiv.permCongr_apply],
       by
        intro i hi
        apply d.pairing.partner_ne ((twoPointLegCongr e).symm i)
        have := congrArg (twoPointLegCongr e).symm hi
        simpa [Equiv.permCongr_apply] using this⟩

@[simp]
theorem TwoPointDiagram.slotCongr_externalLabel (e : ↥T ≃ ↥U)
    (d : TwoPointDiagram ExternalLabel InternalLabel N T) :
    (d.slotCongr (M := M) e).externalLabel = d.externalLabel := rfl

@[simp]
theorem TwoPointDiagram.slotCongr_vertexLabel (e : ↥T ≃ ↥U)
    (d : TwoPointDiagram ExternalLabel InternalLabel N T) (v : ↥U) :
    (d.slotCongr (M := M) e).vertexLabel v = d.vertexLabel (e.symm v) := rfl

/-- The transported pairing pairs the transported legs. -/
theorem TwoPointDiagram.slotCongr_partner (e : ↥T ≃ ↥U)
    (d : TwoPointDiagram ExternalLabel InternalLabel N T)
    (leg : Fin (2 * (2 * T.card + 1))) :
    (d.slotCongr (M := M) e).pairing.partner (twoPointLegCongr e leg) =
      twoPointLegCongr e (d.pairing.partner leg) := by
  change (twoPointLegCongr e).permCongr d.pairing.partner (twoPointLegCongr e leg) = _
  simp [Equiv.permCongr_apply]

/-- **The transport is an isomorphism of vertex graphs.** -/
theorem TwoPointDiagram.slotCongr_adj_iff (e : ↥T ≃ ↥U)
    (d : TwoPointDiagram ExternalLabel InternalLabel N T) (v w : TwoPointVertex T) :
    (d.slotCongr (M := M) e).vertexGraph.Adj
        (twoPointVertexCongr e v) (twoPointVertexCongr e w) ↔
      d.vertexGraph.Adj v w := by
  constructor
  · rintro ⟨hne, leg, hleg, hpartner⟩
    obtain ⟨leg, rfl⟩ := (twoPointLegCongr e).surjective leg
    rw [twoPointVertexOfLeg_twoPointLegCongr] at hleg
    rw [d.slotCongr_partner e leg, twoPointVertexOfLeg_twoPointLegCongr] at hpartner
    exact ⟨fun hvw => hne (congrArg (twoPointVertexCongr e) hvw), leg,
      (twoPointVertexCongr e).injective hleg, (twoPointVertexCongr e).injective hpartner⟩
  · rintro ⟨hne, leg, hleg, hpartner⟩
    refine ⟨fun hEq => hne ((twoPointVertexCongr e).injective hEq), twoPointLegCongr e leg, ?_, ?_⟩
    · rw [twoPointVertexOfLeg_twoPointLegCongr, hleg]
    · rw [d.slotCongr_partner e leg, twoPointVertexOfLeg_twoPointLegCongr, hpartner]

/-- The transport as a graph homomorphism. -/
noncomputable def TwoPointDiagram.slotCongrHom (e : ↥T ≃ ↥U)
    (d : TwoPointDiagram ExternalLabel InternalLabel N T) :
    d.vertexGraph →g (d.slotCongr (M := M) e).vertexGraph where
  toFun := twoPointVertexCongr e
  map_rel' := fun {_ _} hab => (d.slotCongr_adj_iff e _ _).2 hab

/-- The inverse transport as a graph homomorphism. -/
noncomputable def TwoPointDiagram.slotCongrHomSymm (e : ↥T ≃ ↥U)
    (d : TwoPointDiagram ExternalLabel InternalLabel N T) :
    (d.slotCongr (M := M) e).vertexGraph →g d.vertexGraph where
  toFun := (twoPointVertexCongr e).symm
  map_rel' := fun {a b} hab => by
    refine (d.slotCongr_adj_iff (M := M) e _ _).1 ?_
    simpa using hab

/-- **Reachability is preserved by the transport.** -/
theorem TwoPointDiagram.slotCongr_reachable_iff (e : ↥T ≃ ↥U)
    (d : TwoPointDiagram ExternalLabel InternalLabel N T) (v w : TwoPointVertex T) :
    (d.slotCongr (M := M) e).vertexGraph.Reachable
        (twoPointVertexCongr e v) (twoPointVertexCongr e w) ↔
      d.vertexGraph.Reachable v w := by
  constructor
  · intro hreach
    have hmap := hreach.map (d.slotCongrHomSymm (M := M) e)
    have hcoe : ∀ x : TwoPointVertex U,
        (d.slotCongrHomSymm (M := M) e) x = (twoPointVertexCongr e).symm x := fun _ => rfl
    rw [hcoe, hcoe] at hmap
    simpa using hmap
  · intro hreach
    exact hreach.map (d.slotCongrHom (M := M) e)

/-- **Absence of vacuum components is preserved by the transport.** -/
theorem TwoPointDiagram.slotCongr_hasNoVacuumComponent_iff (e : ↥T ≃ ↥U)
    (d : TwoPointDiagram ExternalLabel InternalLabel N T) :
    (d.slotCongr (M := M) e).HasNoVacuumComponent ↔ d.HasNoVacuumComponent := by
  constructor
  · intro hd v
    obtain ⟨f, hf⟩ := hd (e v)
    refine ⟨f, ?_⟩
    rw [← d.slotCongr_reachable_iff (M := M) e (Sum.inl f) (Sum.inr v)]
    simpa using hf
  · intro hd v
    obtain ⟨f, hf⟩ := hd (e.symm v)
    refine ⟨f, ?_⟩
    have := (d.slotCongr_reachable_iff (M := M) e (Sum.inl f) (Sum.inr (e.symm v))).2 hf
    simpa using this

/-- **External connectedness is preserved by the transport.** -/
theorem TwoPointDiagram.slotCongr_isExternallyConnected_iff (e : ↥T ≃ ↥U)
    (d : TwoPointDiagram ExternalLabel InternalLabel N T) :
    (d.slotCongr (M := M) e).IsExternallyConnected ↔ d.IsExternallyConnected := by
  rw [TwoPointDiagram.isExternallyConnected_iff_hasNoVacuumComponent,
    TwoPointDiagram.isExternallyConnected_iff_hasNoVacuumComponent,
    d.slotCongr_hasNoVacuumComponent_iff (M := M) e]

/-- The transport is an equivalence of diagram types. -/
noncomputable def TwoPointDiagram.slotCongrEquiv (e : ↥T ≃ ↥U) :
    TwoPointDiagram ExternalLabel InternalLabel N T ≃
      TwoPointDiagram ExternalLabel InternalLabel M U where
  toFun d := d.slotCongr e
  invFun d := d.slotCongr e.symm
  left_inv d := by
    refine TwoPointDiagram.ext rfl (funext fun v => ?_) ?_
    · simp [TwoPointDiagram.slotCongr]
    · refine Pairing.ext (Equiv.ext fun i => ?_)
      change (twoPointLegCongr e.symm).permCongr
        ((twoPointLegCongr e).permCongr d.pairing.partner) i = _
      rw [twoPointLegCongr_symm]
      simp [Equiv.permCongr_apply]
  right_inv d := by
    refine TwoPointDiagram.ext rfl (funext fun v => ?_) ?_
    · simp [TwoPointDiagram.slotCongr]
    · refine Pairing.ext (Equiv.ext fun i => ?_)
      change (twoPointLegCongr e).permCongr
        ((twoPointLegCongr e.symm).permCongr d.pairing.partner) i = _
      rw [twoPointLegCongr_symm]
      simp [Equiv.permCongr_apply]

end Common
end SecondQuantization
