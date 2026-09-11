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
then reuse Mathlib's `LinearMap.BilinForm.dualSubmodule`.
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
    calc
      inner ℝ G R = (2 * Real.pi) * ((2 * Real.pi)⁻¹ * inner ℝ G R) := by
        field_simp [hpi]
      _ = (2 * Real.pi) * (n : ℝ) := by rw [← hn]
  · intro h R hR
    obtain ⟨n, hn⟩ := h R hR
    apply Submodule.mem_one.mpr
    refine ⟨n, ?_⟩
    rw [reciprocalPairing_apply, hn]
    field_simp [hpi]

end LeanCondensedMatter.Crystal
