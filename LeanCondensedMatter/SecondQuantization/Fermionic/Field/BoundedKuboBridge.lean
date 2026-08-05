import LeanCondensedMatter.SecondQuantization.Fermionic.Field.Peierls
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.OccupationEquivalence
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteHilbertOperatorAlgebra
import LeanCondensedMatter.QuantumTheory.LinearResponse.RetardedSusceptibility

set_option linter.style.header false

/-!
# Bounded finite-lattice bridge for fermionic current response

This module implements the bounded specialization required by F7 of issue #524. The foundational
current remains defined on the basis-independent algebraic exterior Fock space over an arbitrary
locally finite lattice. Here the site type is explicitly finite. The canonical site basis identifies
that exterior Fock representation with the existing occupation-subset representation, and the
repository's finite-Hilbert transport then turns every algebraic endomorphism into a bounded
operator.

The resulting Hilbert space contains all occupation sectors of the finite site cutoff. No fixed
particle-number sector is required for boundedness because the complete finite-lattice fermionic
Fock space is finite-dimensional. This layer does not take a thermodynamic limit and does not claim
that a current-current susceptibility alone is a complete conductivity formula; observable
variation/contact terms remain the responsibility of issue #444.
-/

namespace SecondQuantization
namespace Fermionic
namespace Field

open scoped BigOperators

noncomputable section

/-- The finite-dimensional Hilbert realization of the full fermionic Fock space on a finite site
cutoff. -/
abbrev FiniteLatticeHilbertFock (Site : Type*) [Fintype Site] :=
  Common.FiniteHilbertFock (Occupation Site)

variable {Site : Type*} [LinearOrder Site]

/-- The canonical site basis of finitely supported one-particle lattice states. -/
noncomputable def latticeBasis : Module.Basis Site ℂ (LatticeState Site) :=
  Finsupp.basisSingleOne

/-- The canonical equivalence from occupation-subset Fock space to the exterior-algebra Fock space
for an ordered site type. -/
noncomputable def latticeOccupationEquiv :
    FockSpace Site ≃ₗ[ℂ] FiniteParticleFock (LatticeState Site) :=
  occupationEquiv (latticeBasis (Site := Site))

/-- Conjugate an exterior-Fock endomorphism into the occupation-subset representation. -/
noncomputable def occupationOperator
    (A : FiniteParticleFock (LatticeState Site) →ₗ[ℂ]
      FiniteParticleFock (LatticeState Site)) :
    FockSpace Site →ₗ[ℂ] FockSpace Site :=
  (latticeOccupationEquiv (Site := Site)).symm.toLinearMap.comp
    (A.comp (latticeOccupationEquiv (Site := Site)).toLinearMap)

@[simp]
theorem occupationOperator_add
    (A B : FiniteParticleFock (LatticeState Site) →ₗ[ℂ]
      FiniteParticleFock (LatticeState Site)) :
    occupationOperator (A + B) = occupationOperator A + occupationOperator B := by
  apply LinearMap.ext
  intro Ψ
  simp [occupationOperator, LinearMap.comp_apply]

@[simp]
theorem occupationOperator_smul (c : ℂ)
    (A : FiniteParticleFock (LatticeState Site) →ₗ[ℂ]
      FiniteParticleFock (LatticeState Site)) :
    occupationOperator (c • A) = c • occupationOperator A := by
  apply LinearMap.ext
  intro Ψ
  simp [occupationOperator, LinearMap.comp_apply]

@[simp]
theorem occupationOperator_id :
    occupationOperator
        (LinearMap.id : FiniteParticleFock (LatticeState Site) →ₗ[ℂ]
          FiniteParticleFock (LatticeState Site)) =
      (LinearMap.id : FockSpace Site →ₗ[ℂ] FockSpace Site) := by
  apply LinearMap.ext
  intro Ψ
  simp [occupationOperator]

@[simp]
theorem occupationOperator_comp
    (A B : FiniteParticleFock (LatticeState Site) →ₗ[ℂ]
      FiniteParticleFock (LatticeState Site)) :
    occupationOperator (A.comp B) =
      (occupationOperator A).comp (occupationOperator B) := by
  apply LinearMap.ext
  intro Ψ
  simp [occupationOperator, LinearMap.comp_apply]

/-- Occupation-representation transport bundled as a complex-linear map. -/
noncomputable def occupationOperatorLinearMap :
    (FiniteParticleFock (LatticeState Site) →ₗ[ℂ]
        FiniteParticleFock (LatticeState Site)) →ₗ[ℂ]
      (FockSpace Site →ₗ[ℂ] FockSpace Site) where
  toFun := occupationOperator
  map_add' := occupationOperator_add
  map_smul' := occupationOperator_smul

/-- Occupation-representation transport bundled as a complex algebra homomorphism. -/
noncomputable def occupationOperatorAlgHom :
    (FiniteParticleFock (LatticeState Site) →ₗ[ℂ]
        FiniteParticleFock (LatticeState Site)) →ₐ[ℂ]
      (FockSpace Site →ₗ[ℂ] FockSpace Site) :=
  AlgHom.ofLinearMap
    (occupationOperatorLinearMap (Site := Site))
    occupationOperator_id
    occupationOperator_comp

@[simp]
theorem occupationOperatorAlgHom_apply
    (A : FiniteParticleFock (LatticeState Site) →ₗ[ℂ]
      FiniteParticleFock (LatticeState Site)) :
    occupationOperatorAlgHom A = occupationOperator A :=
  rfl

section FiniteLattice

variable [Fintype Site]

/-- The linear bridge from basis-independent algebraic Fock endomorphisms to bounded operators on
the finite-lattice Hilbert Fock space. -/
noncomputable def boundedLatticeOperatorLinearMap :
    (FiniteParticleFock (LatticeState Site) →ₗ[ℂ]
        FiniteParticleFock (LatticeState Site)) →ₗ[ℂ]
      (FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site) :=
  (Common.finiteHilbertOperatorLinearMap (Config := Occupation Site)).comp
    (occupationOperatorLinearMap (Site := Site))

/-- The complete multiplicative bridge from basis-independent algebraic Fock endomorphisms to
bounded operators on the finite-lattice Hilbert Fock space. -/
noncomputable def boundedLatticeOperatorAlgHom :
    (FiniteParticleFock (LatticeState Site) →ₗ[ℂ]
        FiniteParticleFock (LatticeState Site)) →ₐ[ℂ]
      (FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site) :=
  (Common.finiteHilbertOperatorAlgHom (Config := Occupation Site)).comp
    (occupationOperatorAlgHom (Site := Site))

/-- The bounded finite-lattice realization of an exterior-Fock algebraic endomorphism. -/
noncomputable def boundedLatticeOperator
    (A : FiniteParticleFock (LatticeState Site) →ₗ[ℂ]
      FiniteParticleFock (LatticeState Site)) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  boundedLatticeOperatorLinearMap A

@[simp]
theorem boundedLatticeOperatorAlgHom_apply
    (A : FiniteParticleFock (LatticeState Site) →ₗ[ℂ]
      FiniteParticleFock (LatticeState Site)) :
    boundedLatticeOperatorAlgHom A = boundedLatticeOperator A :=
  rfl

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

/-- The bounded current-current retarded kernel supplied to the general Kubo API.

This is the causal commutator contribution for two derived bond currents. It is deliberately not
named conductivity: a vector-potential response must also account for explicit source dependence of
the measured current, as developed downstream in issue #444. -/
noncomputable def boundedBondCurrentRetardedSusceptibility
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (ℏ q : ℂ) (K : LocallyFiniteHopping Site)
    (x y u v : Site) (t s : ℝ) : ℂ :=
  QuantumTheory.LinearResponse.retardedSusceptibility system expectation
    (boundedBondCurrent ℏ q K x y)
    (boundedBondCurrent ℏ q K u v) t s

end FiniteLattice

end
end Field
end Fermionic
end SecondQuantization
