import LeanCondensedMatter.Analysis.Calculus.AlgebraicDerivative
import LeanCondensedMatter.Analysis.DiscreteLattice
import LeanCondensedMatter.QuantumTheory.PeierlsPhase
import Mathlib.Tactic.Module

set_option linter.style.header false

/-!
# Peierls link Hamiltonians, bond currents, and contact operators

The locally finite one-particle lattice admits oriented Peierls link Hamiltonians, currents,
and the first source variation (contact operator). These algebraic operators and their weak
complex derivatives depend neither on fermionic statistics nor on a Fock-space representation.
Bounded and second-quantized realizations are defined downstream.
-/

namespace LocallyFiniteHopping

open QuantumTheory.PeierlsPhase

variable {Site : Type*} [DecidableEq Site]

/-- The two oriented hopping terms on a link with opposite Peierls phases.

This is the link contribution, not the full hopping Hamiltonian. Link variables remain separate
from a uniform vector potential. Geometric link coordinates and their finite-lattice aggregation
are owned by `Lattice.GeometricCurrent` and `Lattice.GeometricPeierls`; response and conductivity
specializations remain downstream in `Fermionic.Transport`. -/
noncomputable def peierlsBondHamiltonian (K : LocallyFiniteHopping Site)
    (ℏ q : ℂ) (x y : Site) (A : ℂ) :
    (Site →₀ ℂ) →ₗ[ℂ] (Site →₀ ℂ) :=
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
    (Site →₀ ℂ) →ₗ[ℂ] (Site →₀ ℂ) :=
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

/-- Peierls-dependent one-particle current on an oriented bond, defined as the explicit negative
link-Hamiltonian derivative. -/
noncomputable def peierlsBondCurrentOperator (K : LocallyFiniteHopping Site)
    (ℏ q : ℂ) (x y : Site) (A : ℂ) :
    (Site →₀ ℂ) →ₗ[ℂ] (Site →₀ ℂ) :=
  (peierlsCoupling ℏ q * peierlsForwardPhase ℏ q A) •
      (K.amplitude x y • matrixUnit x y) +
    ((-peierlsCoupling ℏ q) * peierlsReversePhase ℏ q A) •
      (K.amplitude y x • matrixUnit y x)

/-- The first source derivative of the Peierls current. Both hopping orientations carry the
coefficient `-(i q / ℏ)²`; it is kept in factorized form to match the derivative construction. -/
noncomputable def oneParticleBondContact (K : LocallyFiniteHopping Site)
    (ℏ q : ℂ) (x y : Site) :
    (Site →₀ ℂ) →ₗ[ℂ] (Site →₀ ℂ) :=
  (peierlsCoupling ℏ q * (-peierlsCoupling ℏ q)) •
      (K.amplitude x y • matrixUnit x y) +
    ((-peierlsCoupling ℏ q) * peierlsCoupling ℏ q) •
      (K.amplitude y x • matrixUnit y x)

/-- The bond contact is the zero-source Peierls bond Hamiltonian multiplied by
`-(i q / ℏ)²`. This is the bond-level diamagnetic identity behind the contact term. -/
theorem oneParticleBondContact_eq_neg_sq_smul_peierlsBondHamiltonian_zero
    (K : LocallyFiniteHopping Site) (ℏ q : ℂ) (x y : Site) :
    K.oneParticleBondContact ℏ q x y =
      (-((peierlsCoupling ℏ q) ^ 2)) •
        K.peierlsBondHamiltonian ℏ q x y 0 := by
  rw [K.peierlsBondHamiltonian_zero]
  unfold oneParticleBondContact
  module

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
