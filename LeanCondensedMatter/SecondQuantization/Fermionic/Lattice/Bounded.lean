import LeanCondensedMatter.QuantumTheory.PeierlsLattice
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.DiscreteLattice
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.FiniteHilbertIsometry
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

/-- The bounded finite-lattice realization of an exterior-Fock algebraic endomorphism. -/
noncomputable def boundedLatticeOperator
    (A : AlgebraicFock ((Site →₀ ℂ)) →ₗ[ℂ]
      AlgebraicFock ((Site →₀ ℂ))) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  AlgebraicFock.finiteHilbertOperatorAlgEquiv (Mode := Site) Finsupp.basisSingleOne A


/-- Finite-lattice second quantization as a complex-linear Lie algebra homomorphism.
It preserves commutators, not products, on the full finite Hilbert Fock space. -/
noncomputable def boundedOneBodyOperator :
    ((Site →₀ ℂ) →ₗ[ℂ] (Site →₀ ℂ)) →ₗ⁅ℂ⁆
      (FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site) where
  toLinearMap := (AlgebraicFock.finiteHilbertOperatorAlgEquiv (Mode := Site) Finsupp.basisSingleOne).toLinearMap.comp
    (AlgebraicFock.dGammaLieHom ((Site →₀ ℂ))).toLinearMap
  map_lie' := by
    intro S T
    change boundedLatticeOperator (AlgebraicFock.dGamma ((Site →₀ ℂ)) ⁅S, T⁆) =
      ⁅boundedLatticeOperator (AlgebraicFock.dGamma ((Site →₀ ℂ)) S),
        boundedLatticeOperator (AlgebraicFock.dGamma ((Site →₀ ℂ)) T)⁆
    rw [← AlgebraicFock.dGamma_lie]
    simp only [boundedLatticeOperator, LieRing.of_associative_ring_bracket, map_sub, map_mul]


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
  change (AlgebraicFock.finiteHilbertOperatorAlgEquiv (Mode := Site) Finsupp.basisSingleOne)
      (AlgebraicFock.dGammaLinear ((Site →₀ ℂ))
        (peierlsCoupling ℏ q • K.bondOperator x y)) =
    (AlgebraicFock.finiteHilbertOperatorAlgEquiv (Mode := Site) Finsupp.basisSingleOne)
      (peierlsCoupling ℏ q • AlgebraicFock.dGamma ((Site →₀ ℂ)) (K.bondOperator x y))
  rw [map_smul, AlgebraicFock.dGammaLinear_apply]

/-- The Peierls derivative/current equivalence survives the finite-dimensional bounded transport. -/
theorem hasAlgebraicDerivAt_boundedPeierlsBondHamiltonian_zero
    (K : LocallyFiniteHopping Site) (ℏ q : ℂ) (x y : Site) :
    HasAlgebraicDerivAt (boundedPeierlsBondHamiltonian K ℏ q x y)
      (-boundedBondCurrent ℏ q K x y) 0 := by
  have h :=
    (K.hasAlgebraicDerivAt_peierlsBondHamiltonian_zero ℏ q x y).map
      (boundedOneBodyOperator (Site := Site)).toLinearMap
  have hcurrent :
      boundedOneBodyOperator (Site := Site) (K.oneParticleBondCurrent ℏ q x y) =
        boundedBondCurrent ℏ q K x y :=
    boundedOneBodyOperator_oneParticleBondCurrent K ℏ q x y
  change HasAlgebraicDerivAt
    (fun A => boundedOneBodyOperator (Site := Site)
      (K.peierlsBondHamiltonian ℏ q x y A))
    (-boundedBondCurrent ℏ q K x y) 0
  simpa only [LieHom.coe_toLinearMap, map_neg, hcurrent] using h

/-- Reversing a bond negates its bounded current observable. -/
theorem boundedBondCurrent_swap (ℏ q : ℂ) (K : LocallyFiniteHopping Site)
    (x y : Site) :
    boundedBondCurrent ℏ q K y x = -boundedBondCurrent ℏ q K x y := by
  change (AlgebraicFock.finiteHilbertOperatorAlgEquiv (Mode := Site) Finsupp.basisSingleOne) (bondCurrent ℏ q K y x) =
    -(AlgebraicFock.finiteHilbertOperatorAlgEquiv (Mode := Site) Finsupp.basisSingleOne) (bondCurrent ℏ q K x y)
  rw [bondCurrent_swap, map_neg]

/-- The algebraic local continuity equation survives exactly in the bounded finite-lattice Hilbert
representation. -/
theorem bounded_discrete_continuity (ℏ q : ℂ)
    (K : LocallyFiniteHopping Site) (x : Site) :
    (Complex.I / ℏ) •
          ⁅boundedHoppingHamiltonian K, boundedLatticeOperator (siteChargeDensity q x)⁆ +
        ∑ y ∈ K.incident x, boundedBondCurrent ℏ q K x y = 0 := by
  have h := congrArg (AlgebraicFock.finiteHilbertOperatorAlgEquiv (Mode := Site) Finsupp.basisSingleOne)
    (discrete_continuity ℏ q K x)
  simpa only [boundedLatticeOperator, boundedHoppingHamiltonian,
    boundedBondCurrent, LieRing.of_associative_ring_bracket,
    map_add, map_smul, map_sum, map_zero, map_sub, map_mul] using h


/-- The finite hopping Hamiltonian is the amplitude-weighted sum of bounded
second-quantized matrix units. -/
theorem boundedHoppingHamiltonian_eq_sum_matrixUnit (K : LocallyFiniteHopping Site) :
    boundedHoppingHamiltonian K =
      ∑ x : Site, ∑ y : Site, K.amplitude x y • boundedOneBodyOperator (matrixUnit x y) := by
  change boundedOneBodyOperator K.operator = _
  rw [K.operator_eq_sum_matrixUnit]
  simp only [map_sum, map_smul]

/-- A site relabeling that preserves the hopping amplitudes fixes the full
finite fermionic hopping Hamiltonian, not only its one-particle matrix. -/
theorem boundedHoppingHamiltonian_siteCovariance
    (K : LocallyFiniteHopping Site) (p : Equiv.Perm Site)
    (Φ : (FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site) →ₗ[ℂ]
      (FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site))
    (hK : ∀ x y, K.amplitude (p x) (p y) = K.amplitude x y)
    (hUnit : ∀ x y, Φ (boundedOneBodyOperator (matrixUnit x y)) =
      boundedOneBodyOperator (matrixUnit (p x) (p y))) :
    Φ (boundedHoppingHamiltonian K) = boundedHoppingHamiltonian K := by
  rw [boundedHoppingHamiltonian_eq_sum_matrixUnit]
  simp only [map_sum, map_smul, hUnit]
  refine Fintype.sum_equiv p _ _ ?_
  intro x
  refine Fintype.sum_equiv p _ _ ?_
  intro y
  rw [hK x y]

/-- Every finite site permutation has a unitary implementation on the full
fermionic occupation Hilbert space, conjugating the bounded second quantization
of each one-particle matrix unit to the relabeled unit. The implementation is
the existing exterior lift of the coordinate-basis isometry, so fermionic
ordering signs are included rather than replaced by a bare occupation permutation. -/
theorem exists_unitary_sitePermutation
    (p : Equiv.Perm Site) :
    ∃ W : FiniteLatticeHilbertFock Site ≃ₗᵢ[ℂ] FiniteLatticeHilbertFock Site,
      ∀ x y : Site, W.conjStarAlgEquiv (boundedOneBodyOperator (matrixUnit x y)) =
        boundedOneBodyOperator (matrixUnit (p x) (p y)) := by
  let b₀ : Module.Basis Site ℂ (Site →₀ ℂ) := Finsupp.basisSingleOne
  let b := Common.finiteHilbertOrthonormalBasis (Config := Site)
  let j : (Site →₀ ℂ) ≃ₗ[ℂ] Common.FiniteHilbertFock Site :=
    Common.finiteHilbertFockEquiv
  let e := b.equiv b p
  let f : (Site →₀ ℂ) →ₗ[ℂ] (Site →₀ ℂ) :=
    (Finsupp.domLCongr p : (Site →₀ ℂ) ≃ₗ[ℂ] (Site →₀ ℂ)).toLinearMap
  have hj (i : Site) : j (b₀ i) = b i := by
    change Common.finiteHilbertFockEquiv (Common.basisState i) =
      Common.finiteHilbertBasisState i
    exact Common.finiteHilbertFockEquiv_basisState i
  have hket (i : Site) : f (latticeKet i) = latticeKet (p i) :=
    Finsupp.domLCongr_single p i (1 : ℂ)
  have hf : e.toLinearEquiv.toLinearMap.comp j.toLinearMap = j.toLinearMap.comp f := by
    apply b₀.ext
    intro i
    change e (j (b₀ i)) = j (f (b₀ i))
    have hi : f (b₀ i) = b₀ (p i) := hket i
    rw [hj i, hi, hj (p i)]
    exact b.equiv_apply_basis b p i
  have hmatrix (x y : Site) :
      f.comp (matrixUnit x y) = (matrixUnit (p x) (p y)).comp f := by
    apply b₀.ext
    intro z
    change f (matrixUnit x y (latticeKet z)) =
      matrixUnit (p x) (p y) (f (latticeKet z))
    rw [hket z]
    by_cases h : z = y
    · subst z
      simp only [matrixUnit_apply, latticeKet, Finsupp.single_eq_same]
      exact hket x
    · have hyz : y ≠ z := Ne.symm h
      have hp : p y ≠ p z := fun heq => hyz (p.injective heq)
      simp [matrixUnit_apply, latticeKet, Finsupp.single_eq_of_ne hyz,
        Finsupp.single_eq_of_ne hp]
  refine ⟨AlgebraicFock.finiteHilbertMap b b e, ?_⟩
  intro x y
  exact AlgebraicFock.finiteHilbertMap_conj_dGamma_of_basis b₀ b j.toLinearMap hj
    e f hf (matrixUnit x y) (matrixUnit (p x) (p y))
    (fun w => DFunLike.congr_fun (hmatrix x y) w)


end FiniteLattice

end
end Lattice
end Fermionic
end SecondQuantization
