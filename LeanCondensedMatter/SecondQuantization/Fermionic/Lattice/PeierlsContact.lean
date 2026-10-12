import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.Bounded

set_option linter.style.header false

/-!
# Bounded Peierls current variation and contact response

For one oriented link, the Peierls Hamiltonian satisfies

```text
H(A) = H(0) - A J₀ + O(A²).
```

The measured current must therefore be treated as the source-dependent family

```text
J(A) = -∂ₐ H(A) = J₀ + A J₁ + O(A²),
```

where `J₁ = -∂ₐ² H(0)`. The one-particle operators and their algebraic derivatives are provided by
`QuantumTheory.PeierlsLattice`. This module transports them through the canonical finite-lattice
bounded one-body realization.

The source derivative remains complexified and algebraic. Observable-variation response
theorems consuming the resulting current and contact operators live downstream in
`Fermionic.Transport`.
-/

noncomputable section



namespace SecondQuantization
namespace Fermionic
namespace Lattice

open QuantumTheory.PeierlsPhase

section Bounded

variable {Site : Type*} [LinearOrder Site] [Fintype Site]

/-- Bounded Peierls-dependent current family on the finite-lattice Hilbert Fock space. -/
noncomputable def boundedPeierlsBondCurrent (K : LocallyFiniteHopping Site)
    (ℏ q : ℂ) (x y : Site) (A : ℂ) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  boundedOneBodyOperator (K.peierlsBondCurrentOperator ℏ q x y A)

/-- Bounded contact operator on the finite-lattice Hilbert Fock space. -/
noncomputable def boundedBondContact (K : LocallyFiniteHopping Site)
    (ℏ q : ℂ) (x y : Site) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  boundedOneBodyOperator (K.oneParticleBondContact ℏ q x y)

/-- The bond-level diamagnetic identity survives the canonical bounded one-body realization. -/
theorem boundedBondContact_eq_neg_sq_smul_peierlsBondHamiltonian_zero
    (K : LocallyFiniteHopping Site) (ℏ q : ℂ) (x y : Site) :
    boundedBondContact K ℏ q x y =
      (-((peierlsCoupling ℏ q) ^ 2)) •
        boundedPeierlsBondHamiltonian K ℏ q x y 0 := by
  rw [boundedBondContact,
    K.oneParticleBondContact_eq_neg_sq_smul_peierlsBondHamiltonian_zero]
  unfold boundedPeierlsBondHamiltonian
  exact map_smul (boundedOneBodyOperatorLinearMap (Site := Site))
    (-((peierlsCoupling ℏ q) ^ 2)) (K.peierlsBondHamiltonian ℏ q x y 0)

/-- At zero source, the bounded Peierls current is the bounded continuity-derived current. -/
@[simp]
theorem boundedPeierlsBondCurrent_zero (K : LocallyFiniteHopping Site)
    (ℏ q : ℂ) (x y : Site) :
    boundedPeierlsBondCurrent K ℏ q x y 0 =
      boundedBondCurrent ℏ q K x y := by
  rw [boundedPeierlsBondCurrent, K.peierlsBondCurrentOperator_zero]
  exact boundedOneBodyOperator_oneParticleBondCurrent K ℏ q x y

/-- The bounded transport preserves the weak algebraic derivative of the Peierls current family. -/
theorem hasAlgebraicDerivAt_boundedPeierlsBondCurrent_zero
    (K : LocallyFiniteHopping Site) (ℏ q : ℂ) (x y : Site) :
    HasAlgebraicDerivAt (boundedPeierlsBondCurrent K ℏ q x y)
      (boundedBondContact K ℏ q x y) 0 := by
  exact (K.hasAlgebraicDerivAt_peierlsBondCurrentOperator_zero ℏ q x y).map
    (boundedOneBodyOperatorLinearMap (Site := Site))

end Bounded

end Lattice
end Fermionic
end SecondQuantization

end
