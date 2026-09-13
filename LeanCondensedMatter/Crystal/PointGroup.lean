/-
Copyright (c) 2026 Naoki Yano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoki Yano
-/
import LeanCondensedMatter.Crystal.Translation
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Point groups of atomic configurations

For an atomic configuration in a real normed affine space, every ambient isometry is affine by the
Mazur–Ulam theorem. Taking its linear isometry part therefore gives a homomorphism from the full
species-preserving symmetry group to the linear-isometry group. Pure translations are exactly the
kernel of this homomorphism, so they form a normal subgroup and the point group is its range.

This formulation keeps nonsymmorphic space-group extensions representable: no splitting or
semidirect-product decomposition is assumed.
-/

namespace LeanCondensedMatter.Crystal

namespace AtomicConfiguration

variable {V E Species : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MetricSpace E] [NormedAddTorsor V E]

noncomputable section

private def symmetryAffineIsometryHom (X : AtomicConfiguration E Species) :
    X.symmetryGroup →* (E ≃ᵃⁱ[ℝ] E) where
  toFun g := (g : E ≃ᵢ E).toRealAffineIsometryEquiv
  map_one' := by
    ext x
    rfl
  map_mul' g h := by
    ext x
    rfl

private def affineIsometryLinearPartHom :
    (E ≃ᵃⁱ[ℝ] E) →* (V ≃ₗᵢ[ℝ] V) where
  toFun e := e.linearIsometryEquiv
  map_one' := by
    ext v
    rfl
  map_mul' e f := by
    ext v
    rfl

/-- The linear isometry carried by each species-preserving configuration symmetry. -/
def symmetryLinearPartHom (X : AtomicConfiguration E Species) :
    X.symmetryGroup →* (V ≃ₗᵢ[ℝ] V) :=
  (affineIsometryLinearPartHom (V := V) (E := E)).comp
    (symmetryAffineIsometryHom (V := V) X)

/-- The crystallographic point group, realized canonically as the image of the linear-part
homomorphism. -/
def pointGroup (X : AtomicConfiguration E Species) : Subgroup (V ≃ₗᵢ[ℝ] V) :=
  (X.symmetryLinearPartHom (V := V)).range

private theorem affineIsometryEquiv_eq_constVAdd_of_linear_eq_one
    (e : E ≃ᵃⁱ[ℝ] E) (h : e.linearIsometryEquiv = 1) :
    ∃ v : V, e = AffineIsometryEquiv.constVAdd ℝ E v := by
  let p : E := Classical.arbitrary E
  refine ⟨e p -ᵥ p, ?_⟩
  ext x
  have hx := e.map_vadd p (x -ᵥ p)
  have hx' : e x = (x -ᵥ p) +ᵥ e p := by
    simpa [h] using hx
  rw [hx']
  apply vsub_left_cancel (p := p)
  change ((x -ᵥ p) +ᵥ e p) -ᵥ p = ((e p -ᵥ p) +ᵥ x) -ᵥ p
  rw [vadd_vsub_assoc, vadd_vsub_assoc, add_comm]

/-- Pure translation symmetries are exactly the kernel of the symmetry linear-part homomorphism. -/
theorem translationSymmetrySubgroup_eq_ker_symmetryLinearPartHom
    (X : AtomicConfiguration E Species) :
    X.translationSymmetrySubgroup (V := V) = (X.symmetryLinearPartHom (V := V)).ker := by
  apply le_antisymm
  · rintro g ⟨v, rfl⟩
    rw [MonoidHom.mem_ker]
    change AffineIsometryEquiv.linearIsometryEquiv
        ((IsometryEquiv.constVAdd (v.toAdd : V) : E ≃ᵢ E).toRealAffineIsometryEquiv) =
      (1 : V ≃ₗᵢ[ℝ] V)
    have hAffine :
        (IsometryEquiv.constVAdd (v.toAdd : V) : E ≃ᵢ E).toRealAffineIsometryEquiv =
          AffineIsometryEquiv.constVAdd ℝ E (v.toAdd : V) := by
      ext x
      rfl
    rw [hAffine]
    rfl
  · intro g hg
    rw [MonoidHom.mem_ker] at hg
    change ((g : E ≃ᵢ E).toRealAffineIsometryEquiv).linearIsometryEquiv = 1 at hg
    obtain ⟨v, hv⟩ :=
      affineIsometryEquiv_eq_constVAdd_of_linear_eq_one
        ((g : E ≃ᵢ E).toRealAffineIsometryEquiv) hg
    have hisometry : (g : E ≃ᵢ E) = IsometryEquiv.constVAdd v := by
      ext x
      have hx := congrArg (fun e : E ≃ᵃⁱ[ℝ] E => e x) hv
      simpa using hx
    have hv_mem : v ∈ X.translationSubgroup (V := V) := by
      rw [mem_translationSubgroup]
      rw [← hisometry]
      exact g.property
    refine ⟨Multiplicative.ofAdd ⟨v, hv_mem⟩, ?_⟩
    apply Subtype.ext
    exact hisometry.symm

/-- The pure-translation subgroup is normal in the full species-preserving symmetry group. -/
instance translationSymmetrySubgroup_normal (X : AtomicConfiguration E Species) :
    (X.translationSymmetrySubgroup (V := V)).Normal := by
  rw [X.translationSymmetrySubgroup_eq_ker_symmetryLinearPartHom (V := V)]
  infer_instance

/-- The quotient of the full symmetry group by pure translations is canonically isomorphic to the
point group. No splitting of this extension is assumed. -/
def quotientTranslationEquivPointGroup (X : AtomicConfiguration E Species) :
    X.symmetryGroup ⧸ X.translationSymmetrySubgroup (V := V) ≃* X.pointGroup (V := V) :=
  (QuotientGroup.quotientMulEquivOfEq
    (X.translationSymmetrySubgroup_eq_ker_symmetryLinearPartHom (V := V))).trans
      (QuotientGroup.quotientKerEquivRange (X.symmetryLinearPartHom (V := V)))

end

end AtomicConfiguration

end LeanCondensedMatter.Crystal
