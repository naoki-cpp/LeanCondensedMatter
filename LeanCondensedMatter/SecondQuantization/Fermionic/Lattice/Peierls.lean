import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.DiscreteLattice
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

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

first on the one-particle algebraic space and then after applying `AlgebraicFock.dGamma` to finite-particle Fock
space. A real physical gauge variable can be recovered by restricting this complexified family to
the real axis; the complex parameter keeps the algebraic derivative statement independent of an
additional real-linear operator layer.
-/

namespace SecondQuantization
namespace Fermionic
namespace Lattice

open scoped BigOperators

variable {V W : Type*}
variable [AddCommGroup V] [Module ℂ V]
variable [AddCommGroup W] [Module ℂ W]

/-- Weak derivative for a family valued in an algebraic complex vector space.

No topology is imposed on `V`. Instead, every algebraic complex-linear functional `V →ₗ[ℂ] ℂ`
must turn the family into an ordinarily complex-differentiable scalar function with the stated
derivative. -/
def HasAlgebraicDerivAt (F : ℂ → V) (F' : V) (A : ℂ) : Prop :=
  ∀ ℓ : V →ₗ[ℂ] ℂ, HasDerivAt (fun z => ℓ (F z)) (ℓ F') A

/-- A scalar differentiable coefficient multiplying a fixed algebraic vector has the expected
algebraic derivative. -/
theorem hasAlgebraicDerivAt_smul_const {f : ℂ → ℂ} {f' A : ℂ}
    (hf : HasDerivAt f f' A) (v : V) :
    HasAlgebraicDerivAt (fun z => f z • v) (f' • v) A := by
  intro ℓ
  simpa only [map_smul] using hf.smul_const (ℓ v)

namespace HasAlgebraicDerivAt

/-- Algebraic derivatives are additive. -/
theorem add {F G : ℂ → V} {F' G' : V} {A : ℂ}
    (hF : HasAlgebraicDerivAt F F' A) (hG : HasAlgebraicDerivAt G G' A) :
    HasAlgebraicDerivAt (fun z => F z + G z) (F' + G') A := by
  intro ℓ
  simpa only [map_add] using (hF ℓ).add (hG ℓ)

/-- A complex-linear map transports algebraic derivatives. -/
theorem map {F : ℂ → V} {F' : V} {A : ℂ}
    (hF : HasAlgebraicDerivAt F F' A) (T : V →ₗ[ℂ] W) :
    HasAlgebraicDerivAt (fun z => T (F z)) (T F') A := by
  intro ℓ
  simpa only [LinearMap.comp_apply] using hF (ℓ.comp T)

end HasAlgebraicDerivAt

/-- The coefficient `i q / ℏ` fixed by the charge and phase convention. -/
noncomputable def peierlsCoupling (ℏ q : ℂ) : ℂ :=
  (Complex.I * q) / ℏ

/-- Peierls phase on the oriented hopping term `h_xy |x><y|`. -/
noncomputable def peierlsForwardPhase (ℏ q A : ℂ) : ℂ :=
  Complex.exp (-(peierlsCoupling ℏ q) * A)

/-- Peierls phase on the oppositely oriented hopping term `h_yx |y><x|`. -/
noncomputable def peierlsReversePhase (ℏ q A : ℂ) : ℂ :=
  Complex.exp (peierlsCoupling ℏ q * A)

@[simp]
theorem peierlsForwardPhase_zero (ℏ q : ℂ) :
    peierlsForwardPhase ℏ q 0 = 1 := by
  simp [peierlsForwardPhase]

@[simp]
theorem peierlsReversePhase_zero (ℏ q : ℂ) :
    peierlsReversePhase ℏ q 0 = 1 := by
  simp [peierlsReversePhase]

private theorem hasDerivAt_exp_const_mul_zero (c : ℂ) :
    HasDerivAt (fun A : ℂ => Complex.exp (c * A)) c 0 := by
  simpa using (hasDerivAt_const_mul (x := (0 : ℂ)) c).cexp

/-- The forward Peierls phase has derivative `-i q / ℏ` at zero. -/
theorem hasDerivAt_peierlsForwardPhase_zero (ℏ q : ℂ) :
    HasDerivAt (peierlsForwardPhase ℏ q) (-(peierlsCoupling ℏ q)) 0 := by
  change HasDerivAt
    (fun A : ℂ => Complex.exp (-(peierlsCoupling ℏ q) * A))
    (-(peierlsCoupling ℏ q)) 0
  exact hasDerivAt_exp_const_mul_zero (-(peierlsCoupling ℏ q))

/-- The reverse Peierls phase has derivative `i q / ℏ` at zero. -/
theorem hasDerivAt_peierlsReversePhase_zero (ℏ q : ℂ) :
    HasDerivAt (peierlsReversePhase ℏ q) (peierlsCoupling ℏ q) 0 := by
  change HasDerivAt
    (fun A : ℂ => Complex.exp (peierlsCoupling ℏ q * A))
    (peierlsCoupling ℏ q) 0
  exact hasDerivAt_exp_const_mul_zero (peierlsCoupling ℏ q)

variable {Site : Type*} [DecidableEq Site]

namespace LocallyFiniteHopping

/-- The two oriented hopping terms on a link with opposite Peierls phases.

This is the link contribution, not the full hopping Hamiltonian. Link variables remain separate
from a uniform vector potential, whose geometric link lengths and directions belong to the
macroscopic conductivity layer. -/
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

/-- The Peierls-coupled link contribution after algebraic second quantization. -/
noncomputable def peierlsBondHamiltonianFock (K : LocallyFiniteHopping Site)
    (ℏ q : ℂ) (x y : Site) (A : ℂ) :
    AlgebraicFock (LatticeState Site) →ₗ[ℂ]
      AlgebraicFock (LatticeState Site) :=
  AlgebraicFock.dGamma (LatticeState Site) (K.peierlsBondHamiltonian ℏ q x y A)

/-- The continuity-derived many-particle bond current is minus the algebraic link derivative of the
Peierls-coupled Fock-space Hamiltonian contribution. -/
theorem hasAlgebraicDerivAt_peierlsBondHamiltonianFock_zero
    (K : LocallyFiniteHopping Site) (ℏ q : ℂ) (x y : Site) :
    HasAlgebraicDerivAt (peierlsBondHamiltonianFock K ℏ q x y)
      (-bondCurrent ℏ q K x y) 0 := by
  have h :=
    (K.hasAlgebraicDerivAt_peierlsBondHamiltonian_zero ℏ q x y).map
      (AlgebraicFock.dGammaLinear (LatticeState Site))
  convert h using 1
  · rfl
  · change
      -bondCurrent ℏ q K x y =
        AlgebraicFock.dGammaLinear (LatticeState Site) (-K.oneParticleBondCurrent ℏ q x y)
    symm
    rw [map_neg]
    unfold LocallyFiniteHopping.oneParticleBondCurrent bondCurrent peierlsCoupling
    rw [map_smul]
    rfl

end Lattice
end Fermionic
end SecondQuantization
