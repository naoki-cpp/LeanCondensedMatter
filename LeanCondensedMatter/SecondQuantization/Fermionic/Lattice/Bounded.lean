import LeanCondensedMatter.QuantumTheory.PeierlsLattice
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.DiscreteLattice
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.OccupationEquivalence
import LeanCondensedMatter.SecondQuantization.Common.Algebra.FiniteHilbertOperator

set_option linter.style.header false

/-!
# Bounded finite-lattice bridge for fermionic current response

The foundational current is defined on the basis-independent algebraic exterior Fock space over an
arbitrary locally finite lattice. Here the site type is explicitly finite. The canonical site basis
identifies that exterior Fock representation with the occupation-subset representation, and the
finite-Hilbert transport turns every algebraic endomorphism into a bounded operator.

Both representation changes are algebra equivalences: conjugation by the occupation/exterior
linear equivalence, followed in finite dimensions by the canonical algebraic-to-bounded Hilbert
transport. Their composition therefore preserves linear combinations, identity, and composition
without coordinate-level proofs.

The resulting Hilbert space contains all occupation sectors of the finite site cutoff. No fixed
particle-number sector is required for boundedness because the complete finite-lattice fermionic
Fock space is finite-dimensional. This layer does not take a thermodynamic limit and does not claim
that a current-current susceptibility alone is a complete conductivity formula; observable
variation/contact terms belong to the conductivity-response layer.
-/

namespace SecondQuantization
namespace Fermionic
namespace Lattice

open QuantumTheory.PeierlsPhase

attribute [local instance 100] LieRing.ofAssociativeRing

open scoped BigOperators

noncomputable section

/-- The finite-dimensional Hilbert realization of the full fermionic Fock space on a site type. The
finiteness assumption is introduced by the bounded transport, not by this type abbreviation. -/
abbrev FiniteLatticeHilbertFock (Site : Type*) :=
  Common.FiniteHilbertFock (Occupation Site)

variable {Site : Type*} [LinearOrder Site]

section FiniteLattice

variable [Fintype Site]

/-- The complete representation transport from basis-independent exterior-Fock endomorphisms to
bounded operators on the finite-lattice Hilbert Fock space. -/
noncomputable def boundedLatticeOperatorAlgEquiv :
    (AlgebraicFock ((Site →₀ ℂ)) →ₗ[ℂ]
        AlgebraicFock ((Site →₀ ℂ))) ≃ₐ[ℂ]
      (FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site) :=
  ((AlgebraicFock.occupationEquiv (Finsupp.basisSingleOne : Module.Basis Site ℂ (Site →₀ ℂ))).symm.conjAlgEquiv ℂ).trans
    (Common.finiteHilbertOperatorAlgEquiv (Config := Occupation Site))

/-- The bounded finite-lattice realization of an exterior-Fock algebraic endomorphism. -/
noncomputable def boundedLatticeOperator
    (A : AlgebraicFock ((Site →₀ ℂ)) →ₗ[ℂ]
      AlgebraicFock ((Site →₀ ℂ))) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  boundedLatticeOperatorAlgEquiv A


/-- Linear finite-lattice realization of an arbitrary one-body operator as a bounded Fock-space
observable. -/
noncomputable def boundedOneBodyOperatorLinearMap :
    ((Site →₀ ℂ) →ₗ[ℂ] (Site →₀ ℂ)) →ₗ[ℂ]
      (FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site) :=
  (boundedLatticeOperatorAlgEquiv (Site := Site)).toLinearMap.comp
    (AlgebraicFock.dGammaLinear ((Site →₀ ℂ)))

/-- Bounded Fock-space observable associated with one supplied one-body operator. -/
noncomputable def boundedOneBodyOperator
    (operator : (Site →₀ ℂ) →ₗ[ℂ] (Site →₀ ℂ)) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  boundedOneBodyOperatorLinearMap operator


/-- Canonical computation rule for the bounded realization of a one-body operator. -/
@[simp]
theorem boundedOneBodyOperator_eq
    (operator : (Site →₀ ℂ) →ₗ[ℂ] (Site →₀ ℂ)) :
    boundedOneBodyOperator operator =
      boundedLatticeOperator
        (AlgebraicFock.dGamma ((Site →₀ ℂ)) operator) :=
  rfl

/-- Bounded many-particle hopping Hamiltonian on the finite-lattice Hilbert Fock space. -/
noncomputable def boundedHoppingHamiltonian (K : LocallyFiniteHopping Site) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  boundedLatticeOperator (hoppingHamiltonian K)

/-- Bounded oriented bond-current observable on the finite-lattice Hilbert Fock space. -/
noncomputable def boundedBondCurrent (ℏ q : ℂ) (K : LocallyFiniteHopping Site)
    (x y : Site) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  boundedLatticeOperator (bondCurrent ℏ q K x y)

/-- Bounded Peierls-coupled link Hamiltonian on the finite-lattice Hilbert Fock space. -/
noncomputable def boundedPeierlsBondHamiltonian (K : LocallyFiniteHopping Site)
    (ℏ q : ℂ) (x y : Site) (A : ℂ) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  boundedOneBodyOperator (K.peierlsBondHamiltonian ℏ q x y A)

/-- Canonical bounded realization of the continuity-derived one-particle bond current.
This identifies the one-body realization with the bounded fermionic current obtained by
second quantization before transport to the finite Hilbert Fock space. -/
theorem boundedOneBodyOperator_oneParticleBondCurrent
    (K : LocallyFiniteHopping Site) (ℏ q : ℂ) (x y : Site) :
    boundedOneBodyOperator (K.oneParticleBondCurrent ℏ q x y) =
      boundedBondCurrent ℏ q K x y := by
  unfold boundedOneBodyOperator boundedOneBodyOperatorLinearMap
  unfold LocallyFiniteHopping.oneParticleBondCurrent boundedBondCurrent bondCurrent peierlsCoupling
  rw [map_smul]
  change
    ((Complex.I * q) / ℏ) •
        boundedLatticeOperator
          (AlgebraicFock.dGamma ((Site →₀ ℂ)) (K.bondOperator x y)) =
      boundedLatticeOperator
        (((Complex.I * q) / ℏ) •
          AlgebraicFock.dGamma ((Site →₀ ℂ)) (K.bondOperator x y))
  change ((Complex.I * q) / ℏ) •
      (boundedLatticeOperatorAlgEquiv (Site := Site))
        (AlgebraicFock.dGamma ((Site →₀ ℂ)) (K.bondOperator x y)) =
    (boundedLatticeOperatorAlgEquiv (Site := Site))
      (((Complex.I * q) / ℏ) •
        AlgebraicFock.dGamma ((Site →₀ ℂ)) (K.bondOperator x y))
  rw [map_smul]

/-- The Peierls derivative/current equivalence survives the finite-dimensional bounded transport. -/
theorem hasAlgebraicDerivAt_boundedPeierlsBondHamiltonian_zero
    (K : LocallyFiniteHopping Site) (ℏ q : ℂ) (x y : Site) :
    HasAlgebraicDerivAt (boundedPeierlsBondHamiltonian K ℏ q x y)
      (-boundedBondCurrent ℏ q K x y) 0 := by
  have h :=
    (K.hasAlgebraicDerivAt_peierlsBondHamiltonian_zero ℏ q x y).map
      (boundedOneBodyOperatorLinearMap (Site := Site))
  have hcurrent :
      boundedOneBodyOperatorLinearMap (Site := Site) (K.oneParticleBondCurrent ℏ q x y) =
        boundedBondCurrent ℏ q K x y :=
    boundedOneBodyOperator_oneParticleBondCurrent K ℏ q x y
  change HasAlgebraicDerivAt
    (fun A => boundedOneBodyOperatorLinearMap (Site := Site)
      (K.peierlsBondHamiltonian ℏ q x y A))
    (-boundedBondCurrent ℏ q K x y) 0
  simpa only [map_neg, hcurrent] using h

/-- Reversing a bond negates its bounded current observable. -/
theorem boundedBondCurrent_swap (ℏ q : ℂ) (K : LocallyFiniteHopping Site)
    (x y : Site) :
    boundedBondCurrent ℏ q K y x = -boundedBondCurrent ℏ q K x y := by
  change (boundedLatticeOperatorAlgEquiv (Site := Site)) (bondCurrent ℏ q K y x) =
    -(boundedLatticeOperatorAlgEquiv (Site := Site)) (bondCurrent ℏ q K x y)
  rw [bondCurrent_swap, map_neg]

/-- The algebraic local continuity equation survives exactly in the bounded finite-lattice Hilbert
representation. -/
theorem bounded_discrete_continuity (ℏ q : ℂ)
    (K : LocallyFiniteHopping Site) (x : Site) :
    (Complex.I / ℏ) •
          ⁅boundedHoppingHamiltonian K, boundedLatticeOperator (siteChargeDensity q x)⁆ +
        ∑ y ∈ K.incident x, boundedBondCurrent ℏ q K x y = 0 := by
  have h := congrArg (boundedLatticeOperatorAlgEquiv (Site := Site))
    (discrete_continuity ℏ q K x)
  simpa only [boundedLatticeOperator, boundedHoppingHamiltonian,
    boundedBondCurrent, LieRing.of_associative_ring_bracket,
    map_add, map_smul, map_sum, map_zero, map_sub, map_mul] using h

end FiniteLattice

end
end Lattice
end Fermionic
end SecondQuantization
