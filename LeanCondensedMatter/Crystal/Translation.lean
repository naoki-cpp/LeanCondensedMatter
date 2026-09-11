/-
Copyright (c) 2026 Naoki Yano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoki Yano
-/
import LeanCondensedMatter.Crystal.Symmetry
import Mathlib.Algebra.Torsor.Basic
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

variable [AddGroup V] [MetricSpace E] [AddTorsor V E] [IsIsometricVAdd V E]

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

end Translation

end AtomicConfiguration

end LeanCondensedMatter.Crystal
