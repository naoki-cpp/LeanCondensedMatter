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

/-- Second quantization of bounded one-body operators preserves the commutator,
although it does not in general preserve operator products. -/
theorem finiteSecondQuantization_lie
    (A B : EuclideanSpace ℂ Site →L[ℂ] EuclideanSpace ℂ Site) :
    finiteSecondQuantization ⁅A, B⁆ =
      ⁅finiteSecondQuantization A, finiteSecondQuantization B⁆ := by
  let e := Common.finiteHilbertOperatorAlgEquiv (Config := Site)
  change boundedOneBodyOperator (e.symm (A * B - B * A)) = _
  rw [map_sub, map_mul, map_mul]
  exact LieHom.map_lie (boundedOneBodyOperator (Site := Site)) _ _

/-- The bounded second quantization acts on the canonical isometric
one-particle embedding as the original bounded operator. This identifies
the actual lattice realization, not a separate occupation-sector model. -/
theorem finiteSecondQuantization_apply_oneParticle
    (A : EuclideanSpace ℂ Site →L[ℂ] EuclideanSpace ℂ Site)
    (v : EuclideanSpace ℂ Site) :
    finiteSecondQuantization A
        (AlgebraicFock.finiteHilbertOneParticleEmbedding
          (Common.finiteHilbertOrthonormalBasis (Config := Site)) v) =
      AlgebraicFock.finiteHilbertOneParticleEmbedding
        (Common.finiteHilbertOrthonormalBasis (Config := Site)) (A v) := by
  let b₀ : Module.Basis Site ℂ (Site →₀ ℂ) := Finsupp.basisSingleOne
  let b := Common.finiteHilbertOrthonormalBasis (Config := Site)
  let j : (Site →₀ ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ Site :=
    Common.finiteHilbertFockEquiv
  have hj (i : Site) : j (b₀ i) = b.toBasis i := by
    change Common.finiteHilbertFockEquiv (Common.basisState i) = b i
    exact Common.finiteHilbertFockEquiv_basisState i
  have hv (w : EuclideanSpace ℂ Site) :
      AlgebraicFock.finiteHilbertOneParticleEmbedding b w =
        AlgebraicFock.finiteHilbertEquiv b₀
          (AlgebraicFock.oneParticle (Site →₀ ℂ) (j.symm w)) := by
    have h := AlgebraicFock.finiteHilbertEquiv_map_of_basis b₀ b.toBasis
      j.toLinearMap hj (AlgebraicFock.oneParticle (Site →₀ ℂ) (j.symm w))
    simpa only [AlgebraicFock.finiteHilbertOneParticleEmbedding_apply,
      AlgebraicFock.oneParticle, ExteriorAlgebra.map_apply_ι, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply] using h
  change finiteSecondQuantization A (AlgebraicFock.finiteHilbertOneParticleEmbedding b v) =
    AlgebraicFock.finiteHilbertOneParticleEmbedding b (A v)
  rw [hv, hv]
  let T := (Common.finiteHilbertOperatorAlgEquiv (Config := Site)).symm A
  change AlgebraicFock.finiteHilbertOperatorAlgEquiv b₀
      (AlgebraicFock.dGamma (Site →₀ ℂ) T)
      (AlgebraicFock.finiteHilbertEquiv b₀
        (AlgebraicFock.oneParticle (Site →₀ ℂ) (j.symm v))) =
    AlgebraicFock.finiteHilbertEquiv b₀
      (AlgebraicFock.oneParticle (Site →₀ ℂ) (j.symm (A v)))
  rw [AlgebraicFock.finiteHilbertOperator_dGamma_oneParticle]
  have hT : j (T (j.symm v)) = A v := by
    have h := congrArg (fun B : EuclideanSpace ℂ Site →L[ℂ] EuclideanSpace ℂ Site =>
      B v) ((Common.finiteHilbertOperatorAlgEquiv (Config := Site)).apply_symm_apply A)
    change j (T (j.symm v)) = A v at h
    exact h
  rw [← hT, j.symm_apply_apply]

/-- Matrix elements in the canonical one-particle sector of the full
finite lattice Fock space are exactly the original bounded matrix elements. -/
theorem inner_finiteSecondQuantization_oneParticle
    (A : EuclideanSpace ℂ Site →L[ℂ] EuclideanSpace ℂ Site)
    (v w : EuclideanSpace ℂ Site) :
    inner ℂ (AlgebraicFock.finiteHilbertOneParticleEmbedding
        (Common.finiteHilbertOrthonormalBasis (Config := Site)) v)
      (finiteSecondQuantization A
        (AlgebraicFock.finiteHilbertOneParticleEmbedding
          (Common.finiteHilbertOrthonormalBasis (Config := Site)) w)) = inner ℂ v (A w) := by
  rw [finiteSecondQuantization_apply_oneParticle]
  exact (AlgebraicFock.finiteHilbertOneParticleEmbedding
    (Common.finiteHilbertOrthonormalBasis (Config := Site))).inner_map_map v (A w)

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

/-- The full-Fock commutator of an exponentially evolved one-body observable
with another one-body observable has the exact one-particle matrix element.
This is the operator/kernel reduction used by a singleton-sector Kubo
calculation; no assumption about a full Fock eigenbasis is required. -/
theorem inner_finiteSecondQuantization_exp_conjugate_lie_oneParticle
    (generator A B : EuclideanSpace ℂ Site →L[ℂ] EuclideanSpace ℂ Site)
    (t : ℝ) (v w : EuclideanSpace ℂ Site) :
    let j := AlgebraicFock.finiteHilbertOneParticleEmbedding
      (Common.finiteHilbertOrthonormalBasis (Config := Site))
    inner ℂ (j v)
      (⁅NormedSpace.exp (t • finiteSecondQuantization generator) *
          finiteSecondQuantization A *
          NormedSpace.exp (-(t • finiteSecondQuantization generator)),
        finiteSecondQuantization B⁆ (j w)) =
      inner ℂ v (⁅NormedSpace.exp (t • generator) * A *
        NormedSpace.exp (-(t • generator)), B⁆ w) := by
  dsimp only
  rw [← finiteSecondQuantization_exp_conjugate, ← finiteSecondQuantization_lie]
  exact inner_finiteSecondQuantization_oneParticle _ v w

end
end SecondQuantization.Fermionic.Lattice
