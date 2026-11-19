import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.TimedField
import Mathlib.GroupTheory.Perm.Sign

set_option linter.style.header false

/-!
# Fixed-time amplitudes for arbitrary external insertions

The canonical fixed flattened leg order is transported to mixed imaginary-time order by
`externalInsertionStandardToMixedAtomicPositionEquiv`. Its permutation sign supplies the fermionic
ordering factor for the full atomic field list. Quartic interaction vertices contribute four
consecutive legs, so no separate interaction-order sign is introduced here.

The fixed-time amplitude is this ordering sign times the generic interaction-vertex weight and the
mixed-time pairing evaluation from `TimedField`.
-/

namespace SecondQuantization
namespace Fermionic

open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- An arbitrary permutation of **quartic interaction vertices** induces
an *even* permutation of their flattened atomic legs. The four local
legs of each vertex retain their order. This is the parity fact
needed to cancel relabeling signs in physical fermionic amplitudes. -/
theorem quarticVertexBlockPermutation_sign_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) :
    Equiv.Perm.sign (p.prodCongr (Equiv.refl (Fin 4))) = 1 := by
  classical
  rw [Equiv.prodCongr_refl_right, Equiv.Perm.sign_prodCongrLeft]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc
    (Equiv.Perm.sign p) ^ 4 =
        ((Equiv.Perm.sign p) ^ 2) ^ 2 := by
          rw [← pow_mul]
    _ = 1 := by simp

/-- The actual flattened-leg transport of an arbitrary external-insertion
diagram is even under any bijection of its interaction vertices.
External insertion positions are fixed and each interaction contributes
four legs, so this does not depend on external field count or the
interaction-subset geometry. -/
theorem externalInsertionLegCongr_sign_eq_one
    {E n : ℕ} {T : Finset (Fin n)}
    (e : ↥T ≃ ↥T) :
    Equiv.Perm.sign (externalInsertionLegCongr (E := E) e) = 1 := by
  classical
  let p : Equiv.Perm (Fin (2 * E) ⊕ (↥T × Fin 4)) :=
    (Equiv.refl (Fin (2 * E))).sumCongr
      (e.prodCongr (Equiv.refl (Fin 4)))
  have hcongr :
      externalInsertionLegCongr (E := E) e =
        (externalInsertionLegEquiv E T).symm.permCongr p := by
    rfl
  rw [hcongr, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr]
  simp [quarticVertexBlockPermutation_sign_eq_one]

/-- Fermionic sign of the permutation from fixed flattened atomic order to mixed-time atomic order. -/
noncomputable def externalInsertionMixedAtomicOrderSign {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) : ℂ :=
  ((Equiv.Perm.sign
    (externalInsertionStandardToMixedAtomicPositionEquiv externalTime σ) : ℤ) : ℂ)


/-- The permutation on *fixed flattened atomic positions* induced by
relabeling interaction vertices. The cardinality cast is needed to
identify the standard `n` slots with the full interaction Finset. -/
noncomputable def externalInsertionStandardSlotPerm
    {E n : ℕ}
    (e : ↥(Finset.univ : Finset (Fin n)) ≃
      ↥(Finset.univ : Finset (Fin n))) :
    Equiv.Perm (Fin (2 * (2 * n + E))) :=
  (finCongr (by simp)).symm.permCongr
    (externalInsertionLegCongr (E := E) e)

/-- Every fixed flattened atomic permutation from relabeling
four-leg interaction vertices is even, for any number of external legs. -/
theorem externalInsertionStandardSlotPerm_sign_eq_one
    {E n : ℕ}
    (e : ↥(Finset.univ : Finset (Fin n)) ≃
      ↥(Finset.univ : Finset (Fin n))) :
    Equiv.Perm.sign (externalInsertionStandardSlotPerm (E := E) e) = 1 := by
  rw [externalInsertionStandardSlotPerm, Equiv.Perm.sign_permCongr]
  exact externalInsertionLegCongr_sign_eq_one e

/-- The original fixed-to-mixed atomic ordering map is obtained by
first permuting the fixed flattened legs and then sorting using the
relabelled interaction times. On injective-time chambers, the
physical mixed-time position permutation itself is the identity. -/
theorem externalInsertionStandardToMixedAtomicPositionEquiv_slotCongr
    {E n : ℕ}
    (e : ↥(Finset.univ : Finset (Fin n)) ≃
      ↥(Finset.univ : Finset (Fin n)))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (hσ : Function.Injective σ) :
    (externalInsertionStandardSlotPerm (E := E) e).trans
        (externalInsertionStandardToMixedAtomicPositionEquiv externalTime
          (σ ∘ fun v => (e.symm ⟨v, Finset.mem_univ v⟩).1)) =
      externalInsertionStandardToMixedAtomicPositionEquiv externalTime σ := by
  let C := externalInsertionOrderedLegSlotCongr (E := E) e
  let L := externalInsertionLegEquiv E (Finset.univ : Finset (Fin n))
  let F : Fin (2 * (2 * n + E)) ≃
      Fin (2 * (2 * (Finset.univ : Finset (Fin n)).card + E)) :=
    finCongr (by simp)
  let M := externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ
  let M' := externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime
    (σ ∘ fun v => (e.symm ⟨v, Finset.mem_univ v⟩).1)
  have hC (x : Fin (2 * (2 * (Finset.univ : Finset (Fin n)).card + E))) :
      L (externalInsertionLegCongr (E := E) e x) = C (L x) := by
    change L ((L.trans (C.trans L.symm)) x) = C (L x)
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
  have hMixed (leg : OrderedExternalInsertionLeg E n) :
      M'.symm (C leg) = M.symm leg := by
    have h := congrArg
      (fun q : Equiv.Perm (Fin (2 * (2 * n + E))) => q (M.symm leg))
      (externalInsertionMixedPositionSlotCongr_eq_refl_of_injective
        e externalTime σ hσ)
    change M'.symm (C (M (M.symm leg))) = M.symm leg at h
    simpa only [Equiv.apply_symm_apply] using h
  apply Equiv.ext
  intro i
  change M'.symm (L (externalInsertionLegCongr (E := E) e (F i))) =
    M.symm (L (F i))
  rw [hC]
  exact hMixed (L (F i))

/-- The physical fermionic ordering sign does not change when four-leg
interaction vertices and their times are permuted together, on any
chamber with pairwise distinct interaction times. This is the
nontrivial sign bridge between #4679's even fixed-leg parity and
#4682's exact identity of mixed-time positions. -/
theorem externalInsertionMixedAtomicOrderSign_slotCongr_of_injective
    {E n : ℕ}
    (e : ↥(Finset.univ : Finset (Fin n)) ≃
      ↥(Finset.univ : Finset (Fin n)))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (hσ : Function.Injective σ) :
    externalInsertionMixedAtomicOrderSign externalTime
        (σ ∘ fun v => (e.symm ⟨v, Finset.mem_univ v⟩).1) =
      externalInsertionMixedAtomicOrderSign externalTime σ := by
  have h := congrArg Equiv.Perm.sign
    (externalInsertionStandardToMixedAtomicPositionEquiv_slotCongr
      e externalTime σ hσ)
  rw [Equiv.Perm.sign_trans,
    externalInsertionStandardSlotPerm_sign_eq_one] at h
  simp only [mul_one] at h
  exact congrArg (fun u : ℤˣ => (u : ℂ)) h

/-- Fixed-time amplitude of an arbitrary external-insertion Wick diagram. -/
noncomputable def ExternalInsertionWickDiagram.fixedTimeAmplitude {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) : ℂ :=
  externalInsertionMixedAtomicOrderSign externalTime σ *
    d.vertexWeight g *
      d.mixedPairingValue ε β externalTime σ

/-- Dyson-signed fixed-time amplitude. The perturbative factor `(-1)^n` is kept separate from
the mixed-time ordering sign carried by `fixedTimeAmplitude`. -/
noncomputable def ExternalInsertionWickDiagram.dysonFixedTimeAmplitude {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) : ℂ :=
  (-1 : ℂ) ^ n * d.fixedTimeAmplitude ε β g externalTime σ


/-- The complete fixed-time physical Wick diagram amplitude, including
its fermionic ordering sign, interaction coupling product, and oriented
free-Gibbs pairing evaluation, is invariant under any permutation of
quartic interaction vertices and their time/label assignments, provided
the interaction times are injective. -/
theorem ExternalInsertionWickDiagram.slotCongr_fixedTimeAmplitude_eq_of_injective
    {E n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (e : ↥(Finset.univ : Finset (Fin n)) ≃
      ↥(Finset.univ : Finset (Fin n)))
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (hσ : Function.Injective σ) :
    ExternalInsertionWickDiagram.fixedTimeAmplitude (d.slotCongr e) ε β g externalTime
        (σ ∘ fun v => (e.symm ⟨v, Finset.mem_univ v⟩).1) =
      d.fixedTimeAmplitude ε β g externalTime σ := by
  simp only [ExternalInsertionWickDiagram.fixedTimeAmplitude,
    externalInsertionMixedAtomicOrderSign_slotCongr_of_injective e externalTime σ hσ,
    d.slotCongr_vertexWeight e g,
    d.slotCongr_mixedPairingValue_eq_of_injective e ε β externalTime σ hσ]

/-- **Full physical Dyson-signed fixed-time amplitude covariance.**
On every strict interaction-time chamber, arbitrary relabeling of
quartic interaction vertices has no effect on the physical amplitude;
the same Dyson factor `(-1)^n` multiplies both sides.

No equality at coincident interaction-vertex times is asserted. Such
collisions are excluded by the strict ordered-simplex congruence
theorem when passing to integrated Dyson contributions. -/
theorem ExternalInsertionWickDiagram.slotCongr_dysonFixedTimeAmplitude_eq_of_injective
    {E n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (e : ↥(Finset.univ : Finset (Fin n)) ≃
      ↥(Finset.univ : Finset (Fin n)))
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (hσ : Function.Injective σ) :
    ExternalInsertionWickDiagram.dysonFixedTimeAmplitude (d.slotCongr e) ε β g externalTime
        (σ ∘ fun v => (e.symm ⟨v, Finset.mem_univ v⟩).1) =
      d.dysonFixedTimeAmplitude ε β g externalTime σ := by
  simp only [ExternalInsertionWickDiagram.dysonFixedTimeAmplitude,
    d.slotCongr_fixedTimeAmplitude_eq_of_injective e ε β g externalTime σ hσ]

end Fermionic
end SecondQuantization
