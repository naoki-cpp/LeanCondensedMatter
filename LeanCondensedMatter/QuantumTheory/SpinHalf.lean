import LeanCondensedMatter.Analysis.InternalSpace.Pauli
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option linter.style.header false

/-!
# Spin-1/2 observables along spin-space components

This module gives the physical spin interpretation of the model-independent Pauli algebra.

Spin components form a real three-dimensional Euclidean vector space. The Pauli matrices enter
only when such a spin-space vector is represented on a two-level spin-1/2 Hilbert space.  Thus the internal Pauli basis is representation data, not the definition of
the polarization component vector itself.

The vector need not be normalized. Unit vectors represent pure polarization directions; arbitrary
vectors retain the linear structure needed for spin components and response tensors.
-/

namespace QuantumTheory
namespace SpinHalf

/-- Real three-dimensional spin-component space. Unit vectors may be interpreted as pure spin
polarization directions, but the linear space itself is the primitive API. -/
abbrev SpinSpace := EuclideanSpace ℝ (Fin 3)


/-- Cartesian coordinate index corresponding to one Pauli-basis axis. This is representation
convention data, not the definition of a spin direction. -/
def cartesianIndex : InternalSpace.PauliAxis → Fin 3
  | .x => 0
  | .y => 1
  | .z => 2

/-- Standard Cartesian basis vector in spin space corresponding to a Pauli-basis axis. -/
noncomputable def cartesianBasisVector (axis : InternalSpace.PauliAxis) : SpinSpace :=
  EuclideanSpace.single (cartesianIndex axis) 1

private def pauliComponent (component : SpinSpace) : InternalSpace.PauliAxis → ℝ
  | .x => component.ofLp 0
  | .y => component.ofLp 1
  | .z => component.ofLp 2

/-- Real-linear spin-1/2 vector observable on spin space,
`S(n) = ℏ (n · σ) / 2`.

The Cartesian coordinates are consumed only inside this representation map; callers supply the spin-space component vector itself. -/
noncomputable def spinMatrix (ℏ : ℝ) :
    SpinSpace →ₗ[ℝ] InternalSpace.PauliMatrix where
  toFun := fun component =>
    (((ℏ / 2 : ℝ) : ℂ)) •
      InternalSpace.pauliCombination (fun axis => (pauliComponent component axis : ℂ))
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


/-- The standard Cartesian spin-space basis is represented by the corresponding Pauli matrix. -/
theorem spinMatrix_cartesianBasisVector (ℏ : ℝ) (axis : InternalSpace.PauliAxis) :
    spinMatrix ℏ (cartesianBasisVector axis) =
      (((ℏ / 2 : ℝ) : ℂ)) • InternalSpace.pauliBasis axis := by
  cases axis <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [spinMatrix, cartesianBasisVector, cartesianIndex, pauliComponent,
      InternalSpace.pauliCombination_eq_components, InternalSpace.pauliBasis,
      InternalSpace.pauliX, InternalSpace.pauliY, InternalSpace.pauliZ]

/-- Spin measured along any real spin-space vector is represented by a Hermitian matrix. -/
theorem spinMatrix_isHermitian (ℏ : ℝ) (component : SpinSpace) :
    (spinMatrix ℏ component).IsHermitian := by
  have hscale : IsSelfAdjoint ((((ℏ / 2 : ℝ) : ℂ))) := by
    simp [isSelfAdjoint_iff]
  exact
    (InternalSpace.pauliCombination_ofReal_isHermitian
      (pauliComponent component)).smul hscale

end SpinHalf
end QuantumTheory
