import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ExternalRestriction
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Diagram

set_option linter.style.header false

/-!
# Reassembling a two-point diagram from an external core and a vacuum remainder

For normalized two-point functions the useful decomposition is binary: one connected component
containing both distinguished external vertices, and the entire remaining vacuum diagram.  The
vacuum remainder need not be decomposed here; the existing quartic linked-cluster machinery already
owns its connected-component decomposition.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

/-- Split the ambient interaction vertices into a chosen external subset and its complement. -/
def TwoPointDiagram.interactionExternalVacuumEquiv
    {S E : Finset (Fin N)} (hE : E ⊆ S) :
    ↥S ≃ ↥E ⊕ ↥(S \ E) where
  toFun v := if hv : v.1 ∈ E then Sum.inl ⟨v.1, hv⟩ else
    Sum.inr ⟨v.1, Finset.mem_sdiff.mpr ⟨v.2, hv⟩⟩
  invFun
    | Sum.inl v => ⟨v.1, hE v.2⟩
    | Sum.inr v => ⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩
  left_inv v := by
    by_cases hv : v.1 ∈ E
    · simp [hv]
    · simp [hv]
  right_inv x := by
    rcases x with v | v
    · simp [v.2]
    · have hv : v.1 ∉ E := (Finset.mem_sdiff.mp v.2).2
      simp [hv]

/-- Split full two-point legs into the external-core two-point legs and vacuum quartic legs. -/
def TwoPointDiagram.externalVacuumLegDataEquiv
    {S E : Finset (Fin N)} (hE : E ⊆ S) :
    TwoPointLeg S ≃ TwoPointLeg E ⊕ (↥(S \ E) × Fin 4) where
  toFun
    | Sum.inl e => Sum.inl (Sum.inl e)
    | Sum.inr (v, l) =>
        match TwoPointDiagram.interactionExternalVacuumEquiv hE v with
        | Sum.inl w => Sum.inl (Sum.inr (w, l))
        | Sum.inr w => Sum.inr (w, l)
  invFun
    | Sum.inl (Sum.inl e) => Sum.inl e
    | Sum.inl (Sum.inr (v, l)) =>
        Sum.inr ((TwoPointDiagram.interactionExternalVacuumEquiv hE).symm (Sum.inl v), l)
    | Sum.inr (v, l) =>
        Sum.inr ((TwoPointDiagram.interactionExternalVacuumEquiv hE).symm (Sum.inr v), l)
  left_inv x := by
    rcases x with e | ⟨v, l⟩
    · rfl
    · cases h : TwoPointDiagram.interactionExternalVacuumEquiv hE v with
      | inl w =>
          simp only
          rw [Equiv.symm_apply_eq]
          exact congrArg Sum.inr (Prod.ext h.symm rfl)
      | inr w =>
          simp only
          rw [Equiv.symm_apply_eq]
          exact congrArg Sum.inr (Prod.ext h.symm rfl)
  right_inv x := by
    rcases x with (e | ⟨v, l⟩) | ⟨v, l⟩
    · rfl
    · simp
    · simp

/-- Flattened ambient legs split into flattened external-core and vacuum legs. -/
noncomputable def TwoPointDiagram.externalVacuumLegEquiv
    {S E : Finset (Fin N)} (hE : E ⊆ S) :
    Fin (2 * (2 * S.card + 1)) ≃
      Fin (2 * (2 * E.card + 1)) ⊕ Fin (2 * (2 * (S \ E).card)) :=
  (twoPointLegEquiv S).trans <|
    (TwoPointDiagram.externalVacuumLegDataEquiv hE).trans <|
      Equiv.sumCongr (twoPointLegEquiv E).symm (quarticLegEquiv (S \ E)).symm

private theorem sumPerm_involutive {α β : Type*}
    (p : Equiv.Perm α) (q : Equiv.Perm β)
    (hp : Function.Involutive p) (hq : Function.Involutive q) :
    Function.Involutive (Equiv.sumCongr p q) := by
  intro x
  rcases x with a | b
  · simp [hp a]
  · simp [hq b]

private theorem sumPerm_ne_self {α β : Type*}
    (p : Equiv.Perm α) (q : Equiv.Perm β)
    (hp : ∀ x, p x ≠ x) (hq : ∀ x, q x ≠ x) :
    ∀ x, Equiv.sumCongr p q x ≠ x
  | Sum.inl a => by simpa using hp a
  | Sum.inr b => by simpa using hq b

private theorem permCongr_involutive {α β : Type*} (e : α ≃ β)
    (p : Equiv.Perm α) (hp : Function.Involutive p) :
    Function.Involutive (e.permCongr p) := by
  intro x
  simp [Equiv.permCongr_apply, hp (e.symm x)]

private theorem permCongr_ne_self {α β : Type*} (e : α ≃ β)
    (p : Equiv.Perm α) (hp : ∀ x, p x ≠ x) (x : β) :
    e.permCongr p x ≠ x := by
  intro h
  rw [Equiv.permCongr_apply, Equiv.apply_eq_iff_eq_symm_apply] at h
  exact hp _ h

/-- Reassemble a full two-point diagram from an externally connected two-point core on `E` and an
arbitrary quartic vacuum diagram on the complementary interaction vertices. -/
noncomputable def TwoPointDiagram.reassembleExternalVacuum
    {S E : Finset (Fin N)} (hE : E ⊆ S)
    (external : ExternallyConnectedTwoPointDiagram ExternalLabel InternalLabel N E)
    (vacuum : QuarticDiagram InternalLabel N (S \ E)) :
    TwoPointDiagram ExternalLabel InternalLabel N S where
  externalLabel := external.1.externalLabel
  vertexLabel v :=
    match TwoPointDiagram.interactionExternalVacuumEquiv hE v with
    | Sum.inl w => external.1.vertexLabel w
    | Sum.inr w => vacuum.vertexLabel w
  pairing := Pairing.ofPartner
    ((TwoPointDiagram.externalVacuumLegEquiv hE).symm.permCongr
      (Equiv.sumCongr external.1.pairing.partner vacuum.pairing.partner))
    ⟨permCongr_involutive _ _
        (sumPerm_involutive _ _ external.1.pairing.partner_involutive
          vacuum.pairing.partner_involutive),
      permCongr_ne_self _ _
        (sumPerm_ne_self _ _ external.1.pairing.partner_ne_self
          vacuum.pairing.partner_ne_self)⟩

@[simp]
theorem TwoPointDiagram.reassembleExternalVacuum_externalLabel
    {S E : Finset (Fin N)} (hE : E ⊆ S)
    (external : ExternallyConnectedTwoPointDiagram ExternalLabel InternalLabel N E)
    (vacuum : QuarticDiagram InternalLabel N (S \ E)) :
    (TwoPointDiagram.reassembleExternalVacuum hE external vacuum).externalLabel =
      external.1.externalLabel :=
  rfl

end Common
end SecondQuantization
