import LeanCondensedMatter.Analysis.Calculus.AlgebraicDerivative
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.DiscreteLattice
import LeanCondensedMatter.QuantumTheory.PeierlsPhase

set_option linter.style.header false

/-!
# Peierls link phases and continuity-derived fermionic current

On the algebraic locally finite lattice layer, the operator spaces are algebraic linear-map spaces
with no chosen norm or topology, so an operator-valued derivative is stated weakly: a family has an
algebraic derivative when every complex-linear scalar functional sees the corresponding ordinary
complex derivative.

For the oriented link `x → y`, the Peierls convention is

```text
h_xy |x><y|  ↦ exp (-(i q / ℏ) A) h_xy |x><y|,
h_yx |y><x|  ↦ exp ( +(i q / ℏ) A) h_yx |y><x|.
```

With this convention, the continuity-derived current satisfies

```text
J_(x→y) = -∂_A H_(x,y)(A) |_(A=0)
```

on the one-particle algebraic space. Finite-particle and bounded finite-lattice realizations apply
the canonical second-quantization and representation transports directly downstream. A real
physical gauge variable can be recovered by restricting this complexified family to the real axis;
the complex parameter keeps the algebraic derivative statement independent of an additional
real-linear operator layer.
-/

namespace LocallyFiniteHopping

open QuantumTheory.PeierlsPhase
open SecondQuantization.Fermionic.Lattice
variable {Site : Type*} [DecidableEq Site]



/-- The two oriented hopping terms on a link with opposite Peierls phases.

This is the link contribution, not the full hopping Hamiltonian. Link variables remain separate
from a uniform vector potential. Geometric link coordinates and their finite-lattice aggregation
are owned by `Lattice.GeometricCurrent` and `Lattice.GeometricPeierls`; response and conductivity
specializations remain downstream in `Fermionic.Transport`. -/
noncomputable def peierlsBondHamiltonian (K : LocallyFiniteHopping Site)
    (ℏ q : ℂ) (x y : Site) (A : ℂ) :
    LatticeState Site →ₗ[ℂ] LatticeState Site :=
  peierlsForwardPhase ℏ q A •
      (K.amplitude x y • matrixUnit x y) +
    peierlsReversePhase ℏ q A •
      (K.amplitude y x • matrixUnit y x)

@[simp]
theorem peierlsBondHamiltonian_zero (K : LocallyFiniteHopping Site)
    (ℏ q : ℂ) (x y : Site) :
    K.peierlsBondHamiltonian ℏ q x y 0 =
      K.amplitude x y • matrixUnit x y +
        K.amplitude y x • matrixUnit y x := by
  simp [peierlsBondHamiltonian]

/-- The one-particle continuity-derived current on an oriented bond. -/
noncomputable def oneParticleBondCurrent (K : LocallyFiniteHopping Site)
    (ℏ q : ℂ) (x y : Site) :
    LatticeState Site →ₗ[ℂ] LatticeState Site :=
  peierlsCoupling ℏ q • K.bondOperator x y

/-- The Peierls link Hamiltonian has derivative equal to minus the one-particle bond current. -/
theorem hasAlgebraicDerivAt_peierlsBondHamiltonian_zero
    (K : LocallyFiniteHopping Site) (ℏ q : ℂ) (x y : Site) :
    HasAlgebraicDerivAt (K.peierlsBondHamiltonian ℏ q x y)
      (-K.oneParticleBondCurrent ℏ q x y) 0 := by
  have hforward := hasAlgebraicDerivAt_smul_const
    (hasDerivAt_peierlsForwardPhase_zero ℏ q)
    (K.amplitude x y • matrixUnit x y)
  have hreverse := hasAlgebraicDerivAt_smul_const
    (hasDerivAt_peierlsReversePhase_zero ℏ q)
    (K.amplitude y x • matrixUnit y x)
  have hsum := hforward.add hreverse
  unfold peierlsBondHamiltonian oneParticleBondCurrent bondOperator
  convert hsum using 1
  rw [smul_sub, neg_sub]
  simp only [neg_smul]
  abel

end LocallyFiniteHopping
