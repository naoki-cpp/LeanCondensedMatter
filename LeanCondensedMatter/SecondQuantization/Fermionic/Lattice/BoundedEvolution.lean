import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.Bounded
import LeanCondensedMatter.Analysis.Calculus.ExponentialConjugation

set_option linter.style.header false

/-! # Finite-Hilbert second quantization and exponential evolution

The one-particle space is Euclidean space on the finite site index. Its canonical algebraic
coordinates feed the existing fermionic second quantization. The resulting continuous linear
map intertwines exponential conjugations because it preserves commutators, not products.
-/

namespace SecondQuantization.Fermionic.Lattice

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

variable {Site : Type*} [LinearOrder Site] [Fintype Site]

/-- Continuous second quantization of bounded operators on the finite one-particle Hilbert space.
The output acts on every occupation sector of the full fermionic Fock space. -/
def finiteSecondQuantization :
    (EuclideanSpace ℂ Site →L[ℂ] EuclideanSpace ℂ Site) →L[ℂ]
      (FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site) :=
  ((boundedOneBodyOperator (Site := Site)).toLinearMap.comp
    (Common.finiteHilbertOperatorAlgEquiv (Config := Site)).symm.toLinearMap).toContinuousLinearMap

/-- The finite Hilbert realization of second quantization preserves commutators. -/
theorem finiteSecondQuantization_lie
    (A B : EuclideanSpace ℂ Site →L[ℂ] EuclideanSpace ℂ Site) :
    finiteSecondQuantization ⁅A, B⁆ =
      ⁅finiteSecondQuantization A, finiteSecondQuantization B⁆ := by
  let e := Common.finiteHilbertOperatorAlgEquiv (Config := Site)
  change boundedOneBodyOperator (e.symm (A * B - B * A)) =
    ⁅boundedOneBodyOperator (e.symm A), boundedOneBodyOperator (e.symm B)⁆
  rw [map_sub, map_mul, map_mul]
  exact LieHom.map_lie (boundedOneBodyOperator (Site := Site)) _ _

/-- Exponential evolution of one-particle observables lifts exactly to the full finite Fock
space. For real-time Hamiltonian evolution, take an imaginary scalar multiple of the Hamiltonian
as `generator`; no self-adjointness is needed for the algebraic conjugation identity itself. -/
theorem finiteSecondQuantization_exp_conjugate
    (generator observable : EuclideanSpace ℂ Site →L[ℂ] EuclideanSpace ℂ Site)
    (t : ℝ) :
    finiteSecondQuantization
        (NormedSpace.exp (t • generator) * observable * NormedSpace.exp (-(t • generator))) =
      NormedSpace.exp (t • finiteSecondQuantization generator) *
        finiteSecondQuantization observable *
          NormedSpace.exp (-(t • finiteSecondQuantization generator)) := by
  apply ContinuousLinearMap.map_exp_conjugate_of_commutator
    ((finiteSecondQuantization (Site := Site)).restrictScalars ℝ) generator
    (finiteSecondQuantization generator) ?_ observable t
  intro x
  exact finiteSecondQuantization_lie generator x

end
end SecondQuantization.Fermionic.Lattice
