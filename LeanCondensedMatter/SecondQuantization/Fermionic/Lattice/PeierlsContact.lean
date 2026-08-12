import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.Bounded

set_option linter.style.header false

/-!
# Peierls current variation and the contact response

For one oriented link, the Peierls Hamiltonian satisfies

```text
H(A) = H(0) - A J₀ + O(A²).
```

The measured current must therefore be treated as the source-dependent family

```text
J(A) = -∂ₐ H(A) = J₀ + A J₁ + O(A²),
```

where `J₁ = -∂ₐ² H(0)`. This module constructs `J(A)` and its algebraic derivative `J₁`, transports
both through `AlgebraicFock.dGamma` and the finite-lattice bounded realization, and specializes the general
observable-variation Kubo theorem. The final response contains both the retarded current-current
kernel and the explicit contact term.

The foundational derivative remains complexified and algebraic. The response theorem uses a real
source profile `f`; at observation time `t`, the affine current coefficient is `f(t) J₁`.
-/

namespace SecondQuantization
namespace Fermionic
namespace Lattice

noncomputable section

section Algebraic

variable {Site : Type*} [DecidableEq Site]

namespace LocallyFiniteHopping

/-- Peierls-dependent one-particle current on an oriented bond, defined as the explicit negative
link-Hamiltonian derivative. -/
noncomputable def peierlsBondCurrentOperator (K : LocallyFiniteHopping Site)
    (ℏ q : ℂ) (x y : Site) (A : ℂ) :
    LatticeState Site →ₗ[ℂ] LatticeState Site :=
  (peierlsCoupling ℏ q * peierlsForwardPhase ℏ q A) •
      (K.amplitude x y • matrixUnit x y) +
    ((-peierlsCoupling ℏ q) * peierlsReversePhase ℏ q A) •
      (K.amplitude y x • matrixUnit y x)

/-- The first source derivative of the Peierls current. Both hopping orientations carry the
coefficient `-(i q / ℏ)²`; it is kept in factorized form to match the derivative construction. -/
noncomputable def oneParticleBondContact (K : LocallyFiniteHopping Site)
    (ℏ q : ℂ) (x y : Site) :
    LatticeState Site →ₗ[ℂ] LatticeState Site :=
  (peierlsCoupling ℏ q * (-peierlsCoupling ℏ q)) •
      (K.amplitude x y • matrixUnit x y) +
    ((-peierlsCoupling ℏ q) * peierlsCoupling ℏ q) •
      (K.amplitude y x • matrixUnit y x)

/-- At zero gauge field, the Peierls current family is the continuity-derived current. -/
@[simp]
theorem peierlsBondCurrentOperator_zero (K : LocallyFiniteHopping Site)
    (ℏ q : ℂ) (x y : Site) :
    K.peierlsBondCurrentOperator ℏ q x y 0 =
      K.oneParticleBondCurrent ℏ q x y := by
  unfold peierlsBondCurrentOperator oneParticleBondCurrent bondOperator
  simp [sub_eq_add_neg]

/-- The source derivative of the Peierls current is the one-particle contact operator. -/
theorem hasAlgebraicDerivAt_peierlsBondCurrentOperator_zero
    (K : LocallyFiniteHopping Site) (ℏ q : ℂ) (x y : Site) :
    HasAlgebraicDerivAt (K.peierlsBondCurrentOperator ℏ q x y)
      (K.oneParticleBondContact ℏ q x y) 0 := by
  have hforward := hasAlgebraicDerivAt_smul_const
    ((hasDerivAt_peierlsForwardPhase_zero ℏ q).const_mul
      (peierlsCoupling ℏ q))
    (K.amplitude x y • matrixUnit x y)
  have hreverse := hasAlgebraicDerivAt_smul_const
    ((hasDerivAt_peierlsReversePhase_zero ℏ q).const_mul
      (-peierlsCoupling ℏ q))
    (K.amplitude y x • matrixUnit y x)
  unfold peierlsBondCurrentOperator oneParticleBondContact
  exact hforward.add hreverse

end LocallyFiniteHopping

/-- Peierls-dependent current after algebraic second quantization. -/
noncomputable def peierlsBondCurrentFock (K : LocallyFiniteHopping Site)
    (ℏ q : ℂ) (x y : Site) (A : ℂ) :
    AlgebraicFock (LatticeState Site) →ₗ[ℂ]
      AlgebraicFock (LatticeState Site) :=
  AlgebraicFock.dGamma (LatticeState Site) (K.peierlsBondCurrentOperator ℏ q x y A)

/-- Many-particle contact operator obtained by second-quantizing the one-particle current
variation. -/
noncomputable def bondContact (K : LocallyFiniteHopping Site)
    (ℏ q : ℂ) (x y : Site) :
    AlgebraicFock (LatticeState Site) →ₗ[ℂ]
      AlgebraicFock (LatticeState Site) :=
  AlgebraicFock.dGamma (LatticeState Site) (K.oneParticleBondContact ℏ q x y)

/-- The Peierls current family agrees with the existing bond current at zero source. -/
@[simp]
theorem peierlsBondCurrentFock_zero (K : LocallyFiniteHopping Site)
    (ℏ q : ℂ) (x y : Site) :
    peierlsBondCurrentFock K ℏ q x y 0 = bondCurrent ℏ q K x y := by
  unfold peierlsBondCurrentFock
  rw [K.peierlsBondCurrentOperator_zero]
  unfold LocallyFiniteHopping.oneParticleBondCurrent bondCurrent peierlsCoupling
  change AlgebraicFock.dGammaLinear (LatticeState Site)
      (((Complex.I * q) / ℏ) • K.bondOperator x y) =
    ((Complex.I * q) / ℏ) • AlgebraicFock.dGamma (LatticeState Site) (K.bondOperator x y)
  rw [map_smul, AlgebraicFock.dGammaLinear_apply]

/-- The Fock-space Peierls current has algebraic derivative equal to the contact operator. -/
theorem hasAlgebraicDerivAt_peierlsBondCurrentFock_zero
    (K : LocallyFiniteHopping Site) (ℏ q : ℂ) (x y : Site) :
    HasAlgebraicDerivAt (peierlsBondCurrentFock K ℏ q x y)
      (bondContact K ℏ q x y) 0 := by
  unfold peierlsBondCurrentFock bondContact
  exact (K.hasAlgebraicDerivAt_peierlsBondCurrentOperator_zero ℏ q x y).map
    (AlgebraicFock.dGammaLinear (LatticeState Site))

end Algebraic

section Bounded

variable {Site : Type*} [LinearOrder Site] [Fintype Site]

/-- Bounded Peierls-dependent current family on the finite-lattice Hilbert Fock space. -/
noncomputable def boundedPeierlsBondCurrent (K : LocallyFiniteHopping Site)
    (ℏ q : ℂ) (x y : Site) (A : ℂ) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  boundedLatticeOperator (peierlsBondCurrentFock K ℏ q x y A)

/-- Bounded contact operator on the finite-lattice Hilbert Fock space. -/
noncomputable def boundedBondContact (K : LocallyFiniteHopping Site)
    (ℏ q : ℂ) (x y : Site) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  boundedLatticeOperator (bondContact K ℏ q x y)

/-- At zero source, the bounded Peierls current is the bounded continuity-derived current. -/
@[simp]
theorem boundedPeierlsBondCurrent_zero (K : LocallyFiniteHopping Site)
    (ℏ q : ℂ) (x y : Site) :
    boundedPeierlsBondCurrent K ℏ q x y 0 =
      boundedBondCurrent ℏ q K x y := by
  unfold boundedPeierlsBondCurrent boundedBondCurrent
  rw [peierlsBondCurrentFock_zero]

/-- The bounded transport preserves the weak algebraic derivative of the Peierls current family. -/
theorem hasAlgebraicDerivAt_boundedPeierlsBondCurrent_zero
    (K : LocallyFiniteHopping Site) (ℏ q : ℂ) (x y : Site) :
    HasAlgebraicDerivAt (boundedPeierlsBondCurrent K ℏ q x y)
      (boundedBondContact K ℏ q x y) 0 := by
  unfold boundedPeierlsBondCurrent boundedBondContact
  exact (hasAlgebraicDerivAt_peierlsBondCurrentFock_zero K ℏ q x y).map
    (boundedLatticeOperatorLinearMap (Site := Site))

end Bounded

end
end Lattice
end Fermionic
end SecondQuantization
