import LeanCondensedMatter.Analysis.InternalSpace.Pauli
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option linter.style.header false

/-!
# Spin-1/2 observables along physical-space directions

This module gives the physical spin interpretation of the model-independent Pauli algebra.

A spin-polarization direction is represented first as a vector in real three-dimensional Euclidean
space.  The Pauli matrices enter only when that physical vector is represented on a two-level
spin-1/2 Hilbert space.  Thus the internal Pauli basis is representation data, not the definition of
the polarization direction itself.

The vector need not be normalized.  Unit vectors represent pure directions, while allowing arbitrary
vectors keeps linear combinations and response-tensor components available without introducing a
separate coordinate-vector API.
-/

namespace QuantumTheory
namespace SpinHalf

/-- Real three-dimensional physical space used to specify a spin-polarization direction. -/
abbrev PhysicalSpace := EuclideanSpace ℝ (Fin 3)

private def pauliComponent (direction : PhysicalSpace) : InternalSpace.PauliAxis → ℝ
  | .x => direction.ofLp 0
  | .y => direction.ofLp 1
  | .z => direction.ofLp 2

/-- Real-linear spin-1/2 vector observable on physical space,
`S(n) = ℏ (n · σ) / 2`.

The Cartesian coordinates are consumed only inside this representation map; callers supply the
physical vector itself. -/
noncomputable def spinMatrix (ℏ : ℝ) :
    PhysicalSpace →ₗ[ℝ] InternalSpace.PauliMatrix where
  toFun := fun direction =>
    (((ℏ / 2 : ℝ) : ℂ)) •
      InternalSpace.pauliCombination (fun axis => (pauliComponent direction axis : ℂ))
  map_add' := by
    intro u v
    have hcoeff :
        (fun axis => (pauliComponent (u + v) axis : ℂ)) =
          (fun axis => (pauliComponent u axis : ℂ)) +
            (fun axis => (pauliComponent v axis : ℂ)) := by
      funext axis
      cases axis <;> simp [pauliComponent]
    rw [hcoeff, InternalSpace.pauliCombination_add, smul_add]
  map_smul' := by
    intro c u
    have hcoeff :
        (fun axis => (pauliComponent (c • u) axis : ℂ)) =
          (c : ℂ) • (fun axis => (pauliComponent u axis : ℂ)) := by
      funext axis
      cases axis <;> simp [pauliComponent]
    rw [hcoeff, InternalSpace.pauliCombination_smul]
    ext i j
    simp
    ring

/-- Spin measured along any real physical-space vector is represented by a Hermitian matrix. -/
theorem spinMatrix_isHermitian (ℏ : ℝ) (direction : PhysicalSpace) :
    (spinMatrix ℏ direction).IsHermitian := by
  have hscale : IsSelfAdjoint ((((ℏ / 2 : ℝ) : ℂ))) := by
    simp [isSelfAdjoint_iff]
  exact
    (InternalSpace.pauliCombination_ofReal_isHermitian
      (pauliComponent direction)).smul hscale

end SpinHalf
end QuantumTheory
