/-
Copyright (c) 2026 Naoki Yano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoki Yano
-/
import LeanCondensedMatter.Crystal.Periodicity
import LeanCondensedMatter.Crystal.PointGroup
import Mathlib.Algebra.Module.Submodule.Map

/-!
# Classification-facing crystal symmetry

The crystallographic point group acts on the translation lattice by integral linear
automorphisms. For a full periodic configuration this representation is faithful, giving the
basis-free form of the usual embedding of a crystallographic point group into `GL(n, ℤ)`.
-/

namespace LeanCondensedMatter.Crystal

namespace AtomicConfiguration

variable {V E Species : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MetricSpace E] [NormedAddTorsor V E]

noncomputable section

private theorem conjugate_constVAdd_eq_constVAdd_linearPart
    (g : E ≃ᵢ E) (v : V) :
    g * (IsometryEquiv.constVAdd v : E ≃ᵢ E) * g⁻¹ =
      IsometryEquiv.constVAdd (g.toRealAffineIsometryEquiv.linearIsometryEquiv v) := by
  ext x
  change g (v +ᵥ g⁻¹ x) = g.toRealAffineIsometryEquiv.linearIsometryEquiv v +ᵥ x
  calc
    g (v +ᵥ g⁻¹ x) =
        g.toRealAffineIsometryEquiv.linearIsometryEquiv v +ᵥ g (g⁻¹ x) := by
      exact g.toRealAffineIsometryEquiv.map_vadd (g⁻¹ x) v
    _ = g.toRealAffineIsometryEquiv.linearIsometryEquiv v +ᵥ x := by simp

/-- The linear part of a configuration symmetry preserves every translation symmetry. -/
theorem symmetryLinearPart_mem_translationSubgroup (X : AtomicConfiguration E Species)
    (g : X.symmetryGroup) {v : V} (hv : v ∈ X.translationSubgroup (V := V)) :
    X.symmetryLinearPartHom (V := V) g v ∈ X.translationSubgroup (V := V) := by
  rw [mem_translationSubgroup]
  change (IsometryEquiv.constVAdd
      (((g : E ≃ᵢ E).toRealAffineIsometryEquiv.linearIsometryEquiv) v) : E ≃ᵢ E) ∈
    X.symmetryGroup
  rw [← conjugate_constVAdd_eq_constVAdd_linearPart (V := V) (g := (g : E ≃ᵢ E)) v]
  exact X.symmetryGroup.mul_mem
    (X.symmetryGroup.mul_mem g.property (mem_translationSubgroup.mp hv))
    (X.symmetryGroup.inv_mem g.property)

/-- A symmetry linear part preserves the translation subgroup in both directions. -/
theorem symmetryLinearPart_mem_translationSubgroup_iff (X : AtomicConfiguration E Species)
    (g : X.symmetryGroup) (v : V) :
    X.symmetryLinearPartHom (V := V) g v ∈ X.translationSubgroup (V := V) ↔
      v ∈ X.translationSubgroup (V := V) := by
  constructor
  · intro hv
    have h := X.symmetryLinearPart_mem_translationSubgroup (V := V) (g := g⁻¹) hv
    simpa using h
  · exact X.symmetryLinearPart_mem_translationSubgroup (V := V) g

/-- Every crystallographic point-group element preserves the translation lattice. -/
theorem pointGroup_mem_translationSubgroup_iff (X : AtomicConfiguration E Species)
    (g : X.pointGroup (V := V)) (v : V) :
    (g : V ≃ₗᵢ[ℝ] V) v ∈ X.translationSubgroup (V := V) ↔
      v ∈ X.translationSubgroup (V := V) := by
  rcases g.property with ⟨s, hs⟩
  have h := X.symmetryLinearPart_mem_translationSubgroup_iff (V := V) s v
  simpa [hs] using h

/-- A point-group element restricted to the translation lattice as a `ℤ`-linear automorphism. -/
def pointGroupLatticeEquiv (X : AtomicConfiguration E Species)
    (g : X.pointGroup (V := V)) :
    AddSubgroup.toIntSubmodule (X.translationSubgroup (V := V)) ≃ₗ[ℤ]
      AddSubgroup.toIntSubmodule (X.translationSubgroup (V := V)) where
  toFun v :=
    ⟨(g : V ≃ₗᵢ[ℝ] V) v,
      (X.pointGroup_mem_translationSubgroup_iff (V := V) g v).2 v.property⟩
  invFun v :=
    ⟨((g⁻¹ : X.pointGroup (V := V)) : V ≃ₗᵢ[ℝ] V) v,
      (X.pointGroup_mem_translationSubgroup_iff (V := V) g⁻¹ v).2 v.property⟩
  left_inv v := by
    apply Subtype.ext
    simp
  right_inv v := by
    apply Subtype.ext
    simp
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' n x := by
    apply Subtype.ext
    simp

/-- The integral representation of the point group on the translation lattice. -/
def pointGroupLatticeRepresentation (X : AtomicConfiguration E Species) :
    X.pointGroup (V := V) →*
      (AddSubgroup.toIntSubmodule (X.translationSubgroup (V := V)) ≃ₗ[ℤ]
        AddSubgroup.toIntSubmodule (X.translationSubgroup (V := V))) where
  toFun := X.pointGroupLatticeEquiv (V := V)
  map_one' := by
    ext v
    rfl
  map_mul' g h := by
    ext v
    rfl

/-- For a full periodic configuration, the point-group action on the translation lattice is
faithful. -/
theorem pointGroupLatticeRepresentation_injective (X : AtomicConfiguration E Species)
    (hX : X.Periodic (V := V)) :
    Function.Injective (X.pointGroupLatticeRepresentation (V := V)) := by
  intro g h hgh
  apply Subtype.ext
  apply LinearIsometryEquiv.ext
  intro x
  have hxspan : x ∈ Submodule.span ℝ
      (AddSubgroup.toIntSubmodule (X.translationSubgroup (V := V)) : Set V) := by
    rw [hX.isZLattice.span_top]
    exact Submodule.mem_top
  induction hxspan using Submodule.span_induction with
  | mem x hx =>
      have heq := DFunLike.congr_fun hgh
        (⟨x, hx⟩ : AddSubgroup.toIntSubmodule (X.translationSubgroup (V := V)))
      exact congrArg Subtype.val heq
  | zero => simp
  | add x y _ _ hx hy => simpa using congrArg₂ (· + ·) hx hy
  | smul a x _ hx => simpa using congrArg (a • ·) hx

end

end AtomicConfiguration

end LeanCondensedMatter.Crystal
