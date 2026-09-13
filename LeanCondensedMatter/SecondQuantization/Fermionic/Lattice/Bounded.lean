import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.Peierls
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.OccupationEquivalence
import LeanCondensedMatter.SecondQuantization.Common.Algebra.FiniteHilbertOperatorAlgebra

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

/-- The canonical equivalence from occupation-subset Fock space to the exterior-algebra Fock space
for an ordered site type. -/
noncomputable def latticeOccupationEquiv :
    OccupationFock Site ≃ₗ[ℂ] AlgebraicFock (LatticeState Site) :=
  AlgebraicFock.occupationEquiv (latticeBasis (Site := Site))

/-- Conjugation by `latticeOccupationEquiv`, as the canonical algebra equivalence from exterior-Fock
endomorphisms to occupation-representation endomorphisms. -/
noncomputable def occupationOperatorAlgEquiv :
    (AlgebraicFock (LatticeState Site) →ₗ[ℂ]
        AlgebraicFock (LatticeState Site)) ≃ₐ[ℂ]
      (OccupationFock Site →ₗ[ℂ] OccupationFock Site) :=
  (latticeOccupationEquiv (Site := Site)).symm.conjAlgEquiv ℂ

/-- Conjugate an exterior-Fock endomorphism into the occupation-subset representation. -/
noncomputable def occupationOperator
    (A : AlgebraicFock (LatticeState Site) →ₗ[ℂ]
      AlgebraicFock (LatticeState Site)) :
    OccupationFock Site →ₗ[ℂ] OccupationFock Site :=
  occupationOperatorAlgEquiv A

/-- Occupation-representation transport bundled as a complex-linear map. -/
noncomputable def occupationOperatorLinearMap :
    (AlgebraicFock (LatticeState Site) →ₗ[ℂ]
        AlgebraicFock (LatticeState Site)) →ₗ[ℂ]
      (OccupationFock Site →ₗ[ℂ] OccupationFock Site) :=
  (occupationOperatorAlgEquiv (Site := Site)).toLinearMap

/-- Occupation-representation transport viewed as a complex algebra homomorphism. -/
noncomputable def occupationOperatorAlgHom :
    (AlgebraicFock (LatticeState Site) →ₗ[ℂ]
        AlgebraicFock (LatticeState Site)) →ₐ[ℂ]
      (OccupationFock Site →ₗ[ℂ] OccupationFock Site) :=
  (occupationOperatorAlgEquiv (Site := Site)).toAlgHom

section FiniteLattice

variable [Fintype Site]

/-- The complete representation transport from basis-independent exterior-Fock endomorphisms to
bounded operators on the finite-lattice Hilbert Fock space. -/
noncomputable def boundedLatticeOperatorAlgEquiv :
    (AlgebraicFock (LatticeState Site) →ₗ[ℂ]
        AlgebraicFock (LatticeState Site)) ≃ₐ[ℂ]
      (FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site) :=
  (occupationOperatorAlgEquiv (Site := Site)).trans
    (Common.finiteHilbertOperatorAlgEquiv (Config := Occupation Site))

/-- The linear bridge from basis-independent algebraic Fock endomorphisms to bounded operators on
the finite-lattice Hilbert Fock space. -/
noncomputable def boundedLatticeOperatorLinearMap :
    (AlgebraicFock (LatticeState Site) →ₗ[ℂ]
        AlgebraicFock (LatticeState Site)) →ₗ[ℂ]
      (FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site) :=
  (boundedLatticeOperatorAlgEquiv (Site := Site)).toLinearMap

/-- The multiplicative bridge from basis-independent algebraic Fock endomorphisms to bounded
operators on the finite-lattice Hilbert Fock space. -/
noncomputable def boundedLatticeOperatorAlgHom :
    (AlgebraicFock (LatticeState Site) →ₗ[ℂ]
        AlgebraicFock (LatticeState Site)) →ₐ[ℂ]
      (FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site) :=
  (boundedLatticeOperatorAlgEquiv (Site := Site)).toAlgHom

/-- The bounded finite-lattice realization of an exterior-Fock algebraic endomorphism. -/
noncomputable def boundedLatticeOperator
    (A : AlgebraicFock (LatticeState Site) →ₗ[ℂ]
      AlgebraicFock (LatticeState Site)) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  boundedLatticeOperatorAlgEquiv A

@[simp]
theorem boundedLatticeOperator_add
    (A B : AlgebraicFock (LatticeState Site) →ₗ[ℂ]
      AlgebraicFock (LatticeState Site)) :
    boundedLatticeOperator (A + B) =
      boundedLatticeOperator A + boundedLatticeOperator B := by
  simpa [boundedLatticeOperator] using
    map_add (boundedLatticeOperatorAlgEquiv (Site := Site)) A B

@[simp]
theorem boundedLatticeOperator_sub
    (A B : AlgebraicFock (LatticeState Site) →ₗ[ℂ]
      AlgebraicFock (LatticeState Site)) :
    boundedLatticeOperator (A - B) =
      boundedLatticeOperator A - boundedLatticeOperator B := by
  simpa [boundedLatticeOperator] using
    map_sub (boundedLatticeOperatorAlgEquiv (Site := Site)) A B

@[simp]
theorem boundedLatticeOperator_smul (c : ℂ)
    (A : AlgebraicFock (LatticeState Site) →ₗ[ℂ]
      AlgebraicFock (LatticeState Site)) :
    boundedLatticeOperator (c • A) = c • boundedLatticeOperator A := by
  simpa [boundedLatticeOperator] using
    map_smul (boundedLatticeOperatorAlgEquiv (Site := Site)) c A

@[simp]
theorem boundedLatticeOperator_zero :
    boundedLatticeOperator
        (0 : AlgebraicFock (LatticeState Site) →ₗ[ℂ]
          AlgebraicFock (LatticeState Site)) = 0 := by
  simpa [boundedLatticeOperator] using
    map_zero (boundedLatticeOperatorAlgEquiv (Site := Site))

@[simp]
theorem boundedLatticeOperator_sum {ι : Type*} (s : Finset ι)
    (F : ι → AlgebraicFock (LatticeState Site) →ₗ[ℂ]
      AlgebraicFock (LatticeState Site)) :
    boundedLatticeOperator (∑ i ∈ s, F i) =
      ∑ i ∈ s, boundedLatticeOperator (F i) := by
  change boundedLatticeOperatorLinearMap (∑ i ∈ s, F i) = _
  rw [map_sum]
  rfl

@[simp]
theorem boundedLatticeOperator_comp
    (A B : AlgebraicFock (LatticeState Site) →ₗ[ℂ]
      AlgebraicFock (LatticeState Site)) :
    boundedLatticeOperator (A.comp B) =
      (boundedLatticeOperator A).comp (boundedLatticeOperator B) := by
  simpa [boundedLatticeOperator] using
    map_mul (boundedLatticeOperatorAlgEquiv (Site := Site)) A B

/-- Bounded transport preserves the ordinary algebraic commutator. -/
theorem boundedLatticeOperator_linearCommutator
    (A B : AlgebraicFock (LatticeState Site) →ₗ[ℂ]
      AlgebraicFock (LatticeState Site)) :
    boundedLatticeOperator (ConservationLaw.linearCommutator A B) =
      (boundedLatticeOperator A).comp (boundedLatticeOperator B) -
        (boundedLatticeOperator B).comp (boundedLatticeOperator A) := by
  unfold ConservationLaw.linearCommutator
  rw [boundedLatticeOperator_sub, boundedLatticeOperator_comp,
    boundedLatticeOperator_comp]

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
  boundedLatticeOperator (peierlsBondHamiltonianFock K ℏ q x y A)

/-- The Peierls derivative/current equivalence survives the finite-dimensional bounded transport. -/
theorem hasAlgebraicDerivAt_boundedPeierlsBondHamiltonian_zero
    (K : LocallyFiniteHopping Site) (ℏ q : ℂ) (x y : Site) :
    HasAlgebraicDerivAt (boundedPeierlsBondHamiltonian K ℏ q x y)
      (-boundedBondCurrent ℏ q K x y) 0 := by
  have h :=
    (hasAlgebraicDerivAt_peierlsBondHamiltonianFock_zero K ℏ q x y).map
      (boundedLatticeOperatorLinearMap (Site := Site))
  change HasAlgebraicDerivAt
    (fun A => boundedLatticeOperatorLinearMap
      (peierlsBondHamiltonianFock K ℏ q x y A))
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
  have h := congrArg (boundedLatticeOperator (Site := Site))
    (discrete_continuity ℏ q K x)
  simpa only [boundedLatticeOperator_add, boundedLatticeOperator_smul,
    boundedLatticeOperator_sum, boundedLatticeOperator_zero,
    boundedLatticeOperator_linearCommutator, boundedHoppingHamiltonian,
    boundedSiteChargeDensity, boundedBondCurrent] using h

end FiniteLattice

end
end Lattice
end Fermionic
end SecondQuantization
