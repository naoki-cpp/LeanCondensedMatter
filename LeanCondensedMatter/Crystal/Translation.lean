/-
Copyright (c) 2026 Naoki Yano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoki Yano
-/
import LeanCondensedMatter.Crystal.Symmetry
import Mathlib.Topology.MetricSpace.IsometricSMul

/-!
# Translation symmetries of atomic configurations

This file extracts the translation symmetries of an atomic configuration from its full geometric
symmetry group. Translation vectors form an additive subgroup of the acting group; periodicity and
lattice structure remain properties to be derived from this subgroup later.
-/

namespace LeanCondensedMatter.Crystal

namespace AtomicConfiguration

variable {V E Species : Type*}

section Translation

variable [AddGroup V] [MetricSpace E] [AddAction V E] [IsIsometricVAdd V E]

/-- The additive subgroup of translation vectors whose induced isometries preserve the atomic
configuration species by species. -/
def translationSubgroup (X : AtomicConfiguration E Species) : AddSubgroup V where
  carrier := {v | (IsometryEquiv.constVAdd v : E ≃ᵢ E) ∈ X.symmetryGroup}
  zero_mem' := by
    change (IsometryEquiv.constVAdd (0 : V) : E ≃ᵢ E) ∈ X.symmetryGroup
    have h : (IsometryEquiv.constVAdd (0 : V) : E ≃ᵢ E) = 1 := by
      ext x
      simp
    rw [h]
    exact X.symmetryGroup.one_mem
  add_mem' {v w} hv hw := by
    change (IsometryEquiv.constVAdd (v + w) : E ≃ᵢ E) ∈ X.symmetryGroup
    have h : (IsometryEquiv.constVAdd (v + w) : E ≃ᵢ E) =
        (IsometryEquiv.constVAdd v : E ≃ᵢ E) * (IsometryEquiv.constVAdd w : E ≃ᵢ E) := by
      ext x
      simp [add_vadd]
    rw [h]
    exact X.symmetryGroup.mul_mem hv hw
  neg_mem' {v} hv := by
    change (IsometryEquiv.constVAdd (-v) : E ≃ᵢ E) ∈ X.symmetryGroup
    have h : (IsometryEquiv.constVAdd (-v) : E ≃ᵢ E) =
        (IsometryEquiv.constVAdd v : E ≃ᵢ E)⁻¹ := by
      ext x
      apply (IsometryEquiv.constVAdd v : E ≃ᵢ E).injective
      simp
    rw [h]
    exact X.symmetryGroup.inv_mem hv

@[simp]
theorem mem_translationSubgroup {X : AtomicConfiguration E Species} {v : V} :
    v ∈ X.translationSubgroup ↔ (IsometryEquiv.constVAdd v : E ≃ᵢ E) ∈ X.symmetryGroup :=
  Iff.rfl

/-- Translation symmetries act canonically on occupied sites. -/
instance translationSiteAddAction (X : AtomicConfiguration E Species) :
    AddAction (X.translationSubgroup (V := V)) X.Site where
  vadd v x :=
    let g : X.symmetryGroup :=
      ⟨IsometryEquiv.constVAdd (v : V), mem_translationSubgroup.1 v.property⟩
    g • x
  zero_vadd x := by
    apply Subtype.ext
    change (0 : V) +ᵥ (x : E) = (x : E)
    simp
  add_vadd v w x := by
    apply Subtype.ext
    change ((v : V) + (w : V)) +ᵥ (x : E) =
      (v : V) +ᵥ ((w : V) +ᵥ (x : E))
    exact add_vadd (v : V) (w : V) (x : E)

@[simp]
theorem coe_vadd_site (X : AtomicConfiguration E Species)
    (v : X.translationSubgroup (V := V)) (x : X.Site) :
    ((v +ᵥ x : X.Site) : E) = (v : V) +ᵥ (x : E) :=
  rfl

/-- A cancellative ambient translation action induces a free translation-symmetry action on
occupied sites. -/
instance translationSiteIsCancelVAdd (X : AtomicConfiguration E Species) [IsCancelVAdd V E] :
    IsCancelVAdd (X.translationSubgroup (V := V)) X.Site where
  left_cancel' v x y h := by
    apply Subtype.ext
    exact IsCancelVAdd.left_cancel (v : V) (x : E) (y : E) <| by
      simpa using congrArg (fun z : X.Site => (z : E)) h
  right_cancel' v w x h := by
    apply Subtype.ext
    exact IsCancelVAdd.right_cancel (v : V) (w : V) (x : E) <| by
      simpa using congrArg (fun z : X.Site => (z : E)) h

/-- Membership in a translation orbit is exactly reachability by a translation symmetry. -/
@[simp]
theorem mem_translation_site_orbit_iff (X : AtomicConfiguration E Species) (x y : X.Site) :
    y ∈ AddAction.orbit (X.translationSubgroup (V := V)) x ↔
      ∃ v : X.translationSubgroup (V := V), (v : V) +ᵥ (x : E) = (y : E) := by
  rw [AddAction.mem_orbit_iff]
  constructor
  · rintro ⟨v, h⟩
    refine ⟨v, ?_⟩
    simpa using congrArg (fun z : X.Site => (z : E)) h
  · rintro ⟨v, h⟩
    refine ⟨v, ?_⟩
    apply Subtype.ext
    simpa using h

/-- Every translation orbit is contained in the corresponding full symmetry orbit. -/
theorem translation_site_orbit_subset_site_orbit (X : AtomicConfiguration E Species) (x : X.Site) :
    AddAction.orbit (X.translationSubgroup (V := V)) x ⊆ MulAction.orbit X.symmetryGroup x := by
  intro y hy
  rcases (X.mem_translation_site_orbit_iff (V := V) x y).1 hy with ⟨v, hv⟩
  refine (X.mem_site_orbit_iff x y).2 ⟨
    ⟨IsometryEquiv.constVAdd (v : V), mem_translationSubgroup.1 v.property⟩, ?_⟩
  simpa using hv

/-- The canonical translation action preserves the species label. -/
@[simp]
theorem species_vadd (X : AtomicConfiguration E Species)
    (v : X.translationSubgroup (V := V)) (x : X.Site) :
    X.species (v +ᵥ x) = X.species x := by
  apply X.species_eq_of_mem_site_orbit
  exact X.translation_site_orbit_subset_site_orbit (V := V) x (AddAction.mem_orbit x v)

end Translation

end AtomicConfiguration

end LeanCondensedMatter.Crystal
