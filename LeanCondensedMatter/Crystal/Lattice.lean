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
membership means that the normalized inner product with every `R ∈ L` is an integer. -/
noncomputable def reciprocalLattice (L : Submodule ℤ V) : Submodule ℤ V :=
  (reciprocalPairing (V := V)).dualSubmodule L

@[simp]
theorem mem_reciprocalLattice {L : Submodule ℤ V} {G : V} :
    G ∈ reciprocalLattice L ↔
      ∀ R ∈ L, reciprocalPairing G R ∈ (1 : Submodule ℤ ℝ) := by
  rfl

end LeanCondensedMatter.Crystal
