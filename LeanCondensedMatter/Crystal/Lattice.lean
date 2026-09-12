/-
Copyright (c) 2026 Naoki Yano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoki Yano
-/
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.BilinearForm.DualLattice

/-!
# Bravais and reciprocal lattices

A Bravais translation lattice is represented directly by Mathlib's canonical full `ℤ`-lattice
substrate

```lean
L : Submodule ℤ V
[DiscreteTopology L]
[IsZLattice ℝ L]
```

rather than by a project-local wrapper type.

For a real inner-product space, the physical reciprocal lattice uses the Bloch wave-vector
convention `exp (i k · R)`. The reciprocal condition is therefore
`⟪G, R⟫ ∈ 2π ℤ`. We encode the `2π` exactly once by normalizing the inner-product bilinear form,
then reuse Mathlib's `LinearMap.BilinForm.dualSubmodule` and dual-basis machinery.
-/

namespace LeanCondensedMatter.Crystal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The Euclidean pairing normalized by `2π`. Integrality of this pairing is the physical
reciprocal-lattice condition for the Bloch convention `exp (i k · R)`. -/
noncomputable def reciprocalPairing : LinearMap.BilinForm ℝ V :=
  (2 * Real.pi)⁻¹ • innerₗ V

@[simp]
theorem reciprocalPairing_apply (G R : V) :
    reciprocalPairing G R = (2 * Real.pi)⁻¹ * inner ℝ G R := by
  simp [reciprocalPairing, smul_eq_mul]

/-- The normalized reciprocal pairing is nondegenerate. -/
theorem reciprocalPairing_nondegenerate :
    (reciprocalPairing (V := V)).Nondegenerate := by
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hinv : (2 * Real.pi : ℝ)⁻¹ ≠ 0 := inv_ne_zero hpi
  constructor
  · intro x hx
    apply ext_inner_right ℝ
    intro y
    have hxy := hx y
    rw [reciprocalPairing_apply] at hxy
    have hinner : inner ℝ x y = 0 := (mul_eq_zero.mp hxy).resolve_left hinv
    simpa using hinner
  · intro y hy
    apply ext_inner_left ℝ
    intro x
    have hxy := hy x
    rw [reciprocalPairing_apply] at hxy
    have hinner : inner ℝ x y = 0 := (mul_eq_zero.mp hxy).resolve_left hinv
    simpa using hinner

/-- The physical reciprocal lattice of a real-space `ℤ`-submodule. For a Bravais lattice `L`,
membership means that the inner product with every `R ∈ L` is an integer multiple of `2π`. -/
noncomputable def reciprocalLattice (L : Submodule ℤ V) : Submodule ℤ V :=
  (reciprocalPairing (V := V)).dualSubmodule L

/-- Physical membership criterion for the reciprocal lattice. This theorem hides the normalized
pairing and Mathlib's unit `ℤ`-submodule from downstream crystal and Bloch consumers. -/
@[simp]
theorem mem_reciprocalLattice {L : Submodule ℤ V} {G : V} :
    G ∈ reciprocalLattice L ↔
      ∀ R ∈ L, ∃ n : ℤ, inner ℝ G R = (2 * Real.pi) * (n : ℝ) := by
  change (∀ R ∈ L, reciprocalPairing G R ∈ (1 : Submodule ℤ ℝ)) ↔ _
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  constructor
  · intro h R hR
    obtain ⟨n, hn⟩ := Submodule.mem_one.mp (h R hR)
    refine ⟨n, ?_⟩
    rw [reciprocalPairing_apply] at hn
    change (n : ℝ) = (2 * Real.pi)⁻¹ * inner ℝ G R at hn
    calc
      inner ℝ G R = (2 * Real.pi) * ((2 * Real.pi)⁻¹ * inner ℝ G R) := by
        field_simp [hpi]
      _ = (2 * Real.pi) * (n : ℝ) := by rw [← hn]
  · intro h R hR
    obtain ⟨n, hn⟩ := h R hR
    apply Submodule.mem_one.mpr
    refine ⟨n, ?_⟩
    change (n : ℝ) = reciprocalPairing G R
    rw [reciprocalPairing_apply, hn]
    field_simp [hpi]

/-- The physical reciprocal basis associated with a finite real basis. It is Mathlib's dual basis
for the normalized reciprocal pairing, so the `2π` convention is inherited from
`reciprocalPairing`. -/
noncomputable def reciprocalBasis {ι : Type*} [Finite ι] (b : Basis ι ℝ V) : Basis ι ℝ V := by
  classical
  exact (reciprocalPairing (V := V)).dualBasis
    (reciprocalPairing_nondegenerate (V := V)) b

/-- A reciprocal basis satisfies the crystallographic pairing relation
`bᵢ · aⱼ = 2π δᵢⱼ`. -/
@[simp]
theorem inner_reciprocalBasis {ι : Type*} [Finite ι] (b : Basis ι ℝ V) (i j : ι) :
    inner ℝ (reciprocalBasis b i) (b j) =
      if i = j then 2 * Real.pi else 0 := by
  classical
  have hpair :
      reciprocalPairing (reciprocalBasis b i) (b j) = if j = i then 1 else 0 := by
    simpa [reciprocalBasis] using
      (LinearMap.BilinForm.apply_dualBasis_left
        (B := reciprocalPairing (V := V))
        (reciprocalPairing_nondegenerate (V := V)) b i j)
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  calc
    inner ℝ (reciprocalBasis b i) (b j) =
        (2 * Real.pi) * reciprocalPairing (reciprocalBasis b i) (b j) := by
      rw [reciprocalPairing_apply]
      field_simp [hpi]
    _ = (2 * Real.pi) * (if j = i then 1 else 0) := by rw [hpair]
    _ = if i = j then 2 * Real.pi else 0 := by simp [eq_comm]

/-- If a real-space lattice is the `ℤ`-span of a finite real basis, its physical reciprocal lattice
is the `ℤ`-span of the corresponding reciprocal basis. -/
theorem reciprocalLattice_span_of_basis {ι : Type*} [Finite ι] (b : Basis ι ℝ V) :
    reciprocalLattice (Submodule.span ℤ (Set.range b)) =
      Submodule.span ℤ (Set.range (reciprocalBasis b)) := by
  classical
  simpa [reciprocalLattice, reciprocalBasis] using
    (LinearMap.BilinForm.dualSubmodule_span_of_basis
      (B := reciprocalPairing (V := V))
      (R := ℤ)
      (reciprocalPairing_nondegenerate (V := V)) b)

end LeanCondensedMatter.Crystal
