import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.BoundedMatrixUnitAdjoint
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.PeierlsContact

set_option linter.style.header false

/-!
# Self-adjoint finite-lattice bond currents from Hermitian hopping

A physical one-particle hopping model has conjugate-transpose matrix elements,

```text
star h_xy = h_yx.
```

For such a model, the oriented hopping difference

```text
h_xy |x><y| - h_yx |y><x|
```

is skew-adjoint after second quantization and finite-Hilbert transport. Multiplication by the pure
imaginary physical factor `i q / ℏ`, with real `q` and `ℏ`, therefore produces a self-adjoint bond
current.

Response theorems consuming these self-adjoint currents live downstream in `Fermionic.Transport`.
-/

noncomputable section

namespace LocallyFiniteHopping

open QuantumTheory.PeierlsPhase
open SecondQuantization.Fermionic.Lattice
variable {Site : Type*} [LinearOrder Site] [Fintype Site]



/-- Coefficient-level Hermiticity of a lattice hopping model. -/
def HasHermitianAmplitudes (K : LocallyFiniteHopping Site) : Prop :=
  ∀ x y : Site, star (K.amplitude x y) = K.amplitude y x

/-- Bounded realization of the second-quantized oriented hopping difference before multiplication
by `i q / ℏ`. -/
noncomputable def boundedBondOperator (K : LocallyFiniteHopping Site) (x y : Site) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  boundedLatticeOperator (AlgebraicFock.dGamma (LatticeState Site) (K.bondOperator x y))

/-- Expand the bounded oriented hopping difference into bounded matrix units. -/
theorem boundedBondOperator_eq (K : LocallyFiniteHopping Site) (x y : Site) :
    K.boundedBondOperator x y =
      K.amplitude x y • boundedDgammaMatrixUnit x y -
        K.amplitude y x • boundedDgammaMatrixUnit y x := by
  unfold boundedBondOperator LocallyFiniteHopping.bondOperator
  have hdGamma :
      AlgebraicFock.dGamma (LatticeState Site)
          (K.amplitude x y • matrixUnit x y -
            K.amplitude y x • matrixUnit y x) =
        K.amplitude x y •
            AlgebraicFock.dGamma (LatticeState Site) (matrixUnit x y) -
          K.amplitude y x •
            AlgebraicFock.dGamma (LatticeState Site) (matrixUnit y x) := by
    change
      AlgebraicFock.dGammaLinear (LatticeState Site)
          (K.amplitude x y • matrixUnit x y -
            K.amplitude y x • matrixUnit y x) = _
    rw [map_sub, map_smul, map_smul]
    rfl
  rw [hdGamma, boundedLatticeOperator_sub,
    boundedLatticeOperator_smul, boundedLatticeOperator_smul]
  rfl

/-- Under Hermitian hopping amplitudes, the oriented hopping difference is skew-adjoint. -/
theorem star_boundedBondOperator
    (K : LocallyFiniteHopping Site) (hK : K.HasHermitianAmplitudes)
    (x y : Site) :
    star (K.boundedBondOperator x y) = -K.boundedBondOperator x y := by
  rw [K.boundedBondOperator_eq]
  simp only [star_sub, star_smul, star_boundedDgammaMatrixUnit, hK x y, hK y x]
  abel

end LocallyFiniteHopping

end
