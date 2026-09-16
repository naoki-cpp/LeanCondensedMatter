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

Response theorems consuming these self-adjoint currents live downstream in `Fermionic.Field`.
-/

namespace SecondQuantization
namespace Fermionic
namespace Lattice

noncomputable section

variable {Site : Type*} [LinearOrder Site] [Fintype Site]

namespace LocallyFiniteHopping

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

/-- The bounded current is the pure-imaginary Peierls coefficient times the bounded oriented
hopping difference. -/
theorem boundedBondCurrent_eq_peierlsCoupling_smul
    (K : LocallyFiniteHopping Site) (ℏ q : ℂ) (x y : Site) :
    boundedBondCurrent ℏ q K x y =
      peierlsCoupling ℏ q • K.boundedBondOperator x y := by
  unfold boundedBondCurrent bondCurrent LocallyFiniteHopping.boundedBondOperator peierlsCoupling
  rw [boundedLatticeOperator_smul]

/-- Physical real parameters automatically give a self-adjoint bounded bond current. -/
theorem isSelfAdjoint_boundedBondCurrent_ofReal
    (K : LocallyFiniteHopping Site) (hK : K.HasHermitianAmplitudes)
    (ℏ q : ℝ) (x y : Site) :
    IsSelfAdjoint (boundedBondCurrent (ℏ : ℂ) (q : ℂ) K x y) := by
  rw [isSelfAdjoint_iff, boundedBondCurrent_eq_peierlsCoupling_smul]
  rw [star_smul, K.star_boundedBondOperator hK]
  have hc : star (peierlsCoupling (ℏ : ℂ) (q : ℂ)) =
      -peierlsCoupling (ℏ : ℂ) (q : ℂ) := by
    simp [peierlsCoupling]
    ring
  rw [hc]
  simp

end
end Lattice
end Fermionic
end SecondQuantization
