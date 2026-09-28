import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.Peierls
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

attribute [local instance 100] LieRing.ofAssociativeRing

open scoped BigOperators

noncomputable section

/-- The finite-dimensional Hilbert realization of the full fermionic Fock space on a site type. The
finiteness assumption is introduced by the bounded transport, not by this type abbreviation. -/
abbrev FiniteLatticeHilbertFock (Site : Type*) :=
  Common.FiniteHilbertFock (Occupation Site)

variable {Site : Type*} [LinearOrder Site]

/-- The canonical site basis of finitely supported one-particle lattice states. -/
noncomputable def latticeBasis : Module.Basis Site ℂ (LatticeState Site) :=
  Finsupp.basisSingleOne

section FiniteLattice

variable [Fintype Site]

/-- The complete representation transport from basis-independent exterior-Fock endomorphisms to
bounded operators on the finite-lattice Hilbert Fock space. -/
noncomputable def boundedLatticeOperatorAlgEquiv :
    (AlgebraicFock (LatticeState Site) →ₗ[ℂ]
        AlgebraicFock (LatticeState Site)) ≃ₐ[ℂ]
      (FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site) :=
  ((AlgebraicFock.occupationEquiv (latticeBasis (Site := Site))).symm.conjAlgEquiv ℂ).trans
    (Common.finiteHilbertOperatorAlgEquiv (Config := Occupation Site))

/-- The linear bridge from basis-independent algebraic Fock endomorphisms to bounded operators on
the finite-lattice Hilbert Fock space. -/
noncomputable def boundedLatticeOperatorLinearMap :
    (AlgebraicFock (LatticeState Site) →ₗ[ℂ]
        AlgebraicFock (LatticeState Site)) →ₗ[ℂ]
      (FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site) :=
  (boundedLatticeOperatorAlgEquiv (Site := Site)).toLinearMap

/-- The bounded finite-lattice realization of an exterior-Fock algebraic endomorphism. -/
noncomputable def boundedLatticeOperator
    (A : AlgebraicFock (LatticeState Site) →ₗ[ℂ]
      AlgebraicFock (LatticeState Site)) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  boundedLatticeOperatorAlgEquiv A

/-- Bounded many-particle hopping Hamiltonian on the finite-lattice Hilbert Fock space. -/
noncomputable def boundedHoppingHamiltonian (K : LocallyFiniteHopping Site) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  boundedLatticeOperator (hoppingHamiltonian K)

/-- Bounded local charge observable on the finite-lattice Hilbert Fock space. -/
noncomputable def boundedSiteChargeDensity (q : ℂ) (x : Site) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  boundedLatticeOperator (siteChargeDensity q x)

/-- Bounded oriented bond-current observable on the finite-lattice Hilbert Fock space. -/
noncomputable def boundedBondCurrent (ℏ q : ℂ) (K : LocallyFiniteHopping Site)
    (x y : Site) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  boundedLatticeOperator (bondCurrent ℏ q K x y)

/-- Bounded Peierls-coupled link Hamiltonian on the finite-lattice Hilbert Fock space. -/
noncomputable def boundedPeierlsBondHamiltonian (K : LocallyFiniteHopping Site)
    (ℏ q : ℂ) (x y : Site) (A : ℂ) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  boundedLatticeOperator
    (AlgebraicFock.dGamma (LatticeState Site) (K.peierlsBondHamiltonian ℏ q x y A))

/-- The Peierls derivative/current equivalence survives the finite-dimensional bounded transport. -/
theorem hasAlgebraicDerivAt_boundedPeierlsBondHamiltonian_zero
    (K : LocallyFiniteHopping Site) (ℏ q : ℂ) (x y : Site) :
    HasAlgebraicDerivAt (boundedPeierlsBondHamiltonian K ℏ q x y)
      (-boundedBondCurrent ℏ q K x y) 0 := by
  have hFock :
      HasAlgebraicDerivAt
        (fun A => AlgebraicFock.dGamma (LatticeState Site)
          (K.peierlsBondHamiltonian ℏ q x y A))
        (-bondCurrent ℏ q K x y) 0 := by
    have h :=
      (K.hasAlgebraicDerivAt_peierlsBondHamiltonian_zero ℏ q x y).map
        (AlgebraicFock.dGammaLinear (LatticeState Site))
    convert h using 1
    · rfl
    · change
        -bondCurrent ℏ q K x y =
          AlgebraicFock.dGammaLinear (LatticeState Site)
            (-K.oneParticleBondCurrent ℏ q x y)
      symm
      rw [map_neg]
      unfold LocallyFiniteHopping.oneParticleBondCurrent bondCurrent peierlsCoupling
      rw [map_smul]
      rfl
  unfold boundedPeierlsBondHamiltonian boundedBondCurrent
  have h := hFock.map (boundedLatticeOperatorLinearMap (Site := Site))
  change HasAlgebraicDerivAt
    (fun A => boundedLatticeOperatorLinearMap
      (AlgebraicFock.dGamma (LatticeState Site) (K.peierlsBondHamiltonian ℏ q x y A)))
    (-boundedLatticeOperatorLinearMap (bondCurrent ℏ q K x y)) 0
  simpa only [map_neg] using h

/-- Reversing a bond negates its bounded current observable. -/
theorem boundedBondCurrent_swap (ℏ q : ℂ) (K : LocallyFiniteHopping Site)
    (x y : Site) :
    boundedBondCurrent ℏ q K y x = -boundedBondCurrent ℏ q K x y := by
  change boundedLatticeOperatorLinearMap (bondCurrent ℏ q K y x) =
    -boundedLatticeOperatorLinearMap (bondCurrent ℏ q K x y)
  rw [bondCurrent_swap, map_neg]

/-- The algebraic local continuity equation survives exactly in the bounded finite-lattice Hilbert
representation. -/
theorem bounded_discrete_continuity (ℏ q : ℂ)
    (K : LocallyFiniteHopping Site) (x : Site) :
    (Complex.I / ℏ) •
          ((boundedHoppingHamiltonian K).comp (boundedSiteChargeDensity q x) -
            (boundedSiteChargeDensity q x).comp (boundedHoppingHamiltonian K)) +
        ∑ y ∈ K.incident x, boundedBondCurrent ℏ q K x y = 0 := by
  have h := congrArg (boundedLatticeOperatorAlgEquiv (Site := Site))
    (discrete_continuity ℏ q K x)
  simpa only [map_add, map_smul, map_sum, map_zero,
    LieRing.of_associative_ring_bracket, ← Module.End.mul_eq_comp,
    map_sub, map_mul, ← ContinuousLinearMap.mul_def,
    boundedHoppingHamiltonian, boundedSiteChargeDensity, boundedBondCurrent,
    boundedLatticeOperator] using h

end FiniteLattice

end
end Lattice
end Fermionic
end SecondQuantization
