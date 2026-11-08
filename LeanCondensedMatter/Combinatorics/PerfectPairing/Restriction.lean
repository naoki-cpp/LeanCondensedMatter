import LeanCondensedMatter.Combinatorics.PerfectPairing.Transport

set_option linter.style.header false

/-!
# Restricting a pairing to an invariant subtype

A `PairingOn α` can be restricted to any partner-invariant predicate on `α`. The canonical
restriction is itself a `PairingOn` on the invariant subtype; an arbitrary equivalence may then
transport that pairing to any target type.

The ordered finite `Pairing n` inherits this construction directly. Diagrammatic users remain
responsible only for the invariant predicate and their domain-specific reindexing equivalence.
-/

namespace Combinatorics

/-- Restrict a pairing to a partner-invariant subtype. -/
noncomputable def PairingOn.restrict {α : Type*} (pairing : PairingOn α)
    (p : α → Prop) (hpartner : ∀ i, p i ↔ p (pairing.partner i)) :
    PairingOn {i : α // p i} where
  partner := pairing.partner.subtypePerm fun i => (hpartner i).symm
  partner_involutive := by
    intro i
    apply Subtype.ext
    simp only [Equiv.Perm.subtypePerm_apply]
    exact pairing.partner_involutive i
  partner_ne := by
    intro i hi
    apply pairing.partner_ne i
    have hv := congrArg Subtype.val hi
    simpa only [Equiv.Perm.subtypePerm_apply] using hv

/-- The restricted pairing has the ambient partner as its underlying value. -/
@[simp]
theorem PairingOn.restrict_partner_val {α : Type*} (pairing : PairingOn α)
    (p : α → Prop) (hpartner : ∀ i, p i ↔ p (pairing.partner i))
    (i : {i : α // p i}) :
    (((pairing.restrict p hpartner).partner i : {i : α // p i}) : α) =
      pairing.partner i :=
  congrArg Subtype.val
    (Equiv.Perm.subtypePerm_apply pairing.partner (fun x => (hpartner x).symm) i)

/-- Restrict a pairing to a partner-invariant subtype and transport the result along an arbitrary
equivalence to the target type. -/
noncomputable def PairingOn.restrictAlongEquiv {α β : Type*} (pairing : PairingOn α)
    (p : α → Prop) (hpartner : ∀ i, p i ↔ p (pairing.partner i))
    (e : {i : α // p i} ≃ β) : PairingOn β :=
  (pairing.restrict p hpartner).transport e.symm

/-- The transported restricted pairing agrees with the restricted partner under the chosen
equivalence. -/
@[simp]
theorem PairingOn.restrictAlongEquiv_partner {α β : Type*} (pairing : PairingOn α)
    (p : α → Prop) (hpartner : ∀ i, p i ↔ p (pairing.partner i))
    (e : {i : α // p i} ≃ β)
    (i : {i : α // p i}) :
    (pairing.restrictAlongEquiv p hpartner e).partner (e i) =
      e ((pairing.restrict p hpartner).partner i) := by
  simp [PairingOn.restrictAlongEquiv]


/-- Transporting a restricted partner back to the ambient subtype recovers the ambient partner
as its underlying value. -/
@[simp]
theorem PairingOn.restrictAlongEquiv_partner_symm_val {α β : Type*} (pairing : PairingOn α)
    (p : α → Prop) (hpartner : ∀ i, p i ↔ p (pairing.partner i))
    (e : {i : α // p i} ≃ β) (i : β) :
    ((e.symm ((pairing.restrictAlongEquiv p hpartner e).partner i) :
        {i : α // p i}) : α) =
      pairing.partner (e.symm i) := by
  let j := e.symm i
  have h := pairing.restrictAlongEquiv_partner p hpartner e j
  have h' := congrArg (fun q => ((e.symm q : {i : α // p i}) : α)) h
  simpa [j] using h'



/-- Extract the fiber over a fixed index from a dependent sigma type.
This is the canonical transport used when restricting a pairing which
never connects different sigma fibers. -/
private def sigmaFiberEquiv {ι : Type*} {β : ι → Type*} (i : ι) :
    {x : Σ j, β j // x.1 = i} ≃ β i where
  toFun := fun x => x.2 ▸ x.1.2
  invFun := fun x => ⟨⟨i, x⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨j, x⟩, h⟩
    cases h
    rfl
  right_inv := fun _ => rfl

/-- Restrict a perfect pairing on a dependent disjoint union to one
fiber when partners preserve the fiber index. -/
noncomputable def PairingOn.sigmaFiberPairing
    {ι : Type*} {β : ι → Type*}
    (P : PairingOn (Σ i, β i))
    (h : ∀ x, (P.partner x).1 = x.1) (i : ι) :
    PairingOn (β i) :=
  P.restrictAlongEquiv
    (fun x => x.1 = i)
    (fun x => by rw [h x])
    (sigmaFiberEquiv i)

/-- The local partner, inserted back into its sigma fiber, equals
the original global partner. -/
theorem PairingOn.sigmaFiberPairing_partner
    {ι : Type*} {β : ι → Type*}
    (P : PairingOn (Σ i, β i))
    (h : ∀ x, (P.partner x).1 = x.1) (i : ι) (x : β i) :
    P.partner ⟨i, x⟩ = ⟨i, (P.sigmaFiberPairing h i).partner x⟩ := by
  have hp := P.restrictAlongEquiv_partner_symm_val
    (fun z : Σ j, β j => z.1 = i)
    (fun z => by rw [h z])
    (sigmaFiberEquiv i) x
  exact hp.symm

/-- A pairing which preserves the indices of a dependent sum is precisely
the disjoint union of its restrictions to the individual fibers. -/
theorem PairingOn.sigmaCongrRight_sigmaFiberPairing
    {ι : Type*} {β : ι → Type*}
    (P : PairingOn (Σ i, β i))
    (h : ∀ x, (P.partner x).1 = x.1) :
    PairingOn.sigmaCongrRight (P.sigmaFiberPairing h) = P := by
  apply PairingOn.ext
  apply Equiv.ext
  rintro ⟨i, x⟩
  simpa only [PairingOn.sigmaCongrRight_partner] using
    (P.sigmaFiberPairing_partner h i x).symm

end Combinatorics
