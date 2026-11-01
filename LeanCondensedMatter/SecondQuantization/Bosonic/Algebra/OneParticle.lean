import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.FiniteModes
import Mathlib.LinearAlgebra.Finsupp.Supported

set_option linter.style.header false

/-!
# The one-particle embedding into algebraic bosonic Fock space

A finite one-particle amplitude is sent to the same linear combination of occupation
states with one boson. The map is injective and intertwines every one-particle
endomorphism with its number-conserving second quantization. No completed-space
inner product or isometry is asserted.
-/

namespace SecondQuantization.Bosonic

open scoped BigOperators
noncomputable section
variable {Mode : Type*} [Fintype Mode]

/-- File-local classical decidable equality matching finite-mode second quantization. -/
local instance instDecidableEqOneParticle : DecidableEq Mode := Classical.decEq Mode

/-- The linear embedding of site amplitudes as superpositions of one-boson occupations. -/
def oneParticleEmbedding : EuclideanSpace ℂ Mode →ₗ[ℂ] FockSpace Mode where
  toFun v := ∑ i, v i • basisState (singleOccupation i)
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.smul_sum, smul_smul]

/-- The one-particle embedding sends a site basis vector to its one-boson occupation state. -/
@[simp]
theorem oneParticleEmbedding_single (i : Mode) :
    oneParticleEmbedding (EuclideanSpace.single i 1) = basisState (singleOccupation i) := by
  simp [oneParticleEmbedding, PiLp.single_apply, ite_smul]

/-- The embedded vector is obtained by creating that one-particle amplitude from the vacuum. -/
theorem createVector_fockVacuum (v : EuclideanSpace ℂ Mode) :
    createVector v fockVacuum = oneParticleEmbedding v := by
  simp [createVector, oneParticleEmbedding, LinearMap.sum_apply]

private theorem annihilate_basisState_singleOccupation (i j : Mode) :
    annihilate i (basisState (singleOccupation j)) =
      if i = j then fockVacuum else 0 := by
  have h := LinearMap.congr_fun (comm_annihilate_create i j) fockVacuum
  by_cases hij : i = j
  · simpa [hij, ScalarExchange.zetaCommutator_apply] using h
  · simpa [hij, ScalarExchange.zetaCommutator_apply] using h

/-- Annihilation recovers the corresponding one-particle amplitude as a vacuum coefficient. -/
@[simp]
theorem annihilate_oneParticleEmbedding (i : Mode) (v : EuclideanSpace ℂ Mode) :
    annihilate i (oneParticleEmbedding v) = v i • fockVacuum := by
  simp [oneParticleEmbedding, map_sum, map_smul,
    annihilate_basisState_singleOccupation, smul_ite]

/-- Distinct one-particle amplitudes define distinct algebraic one-boson states. -/
theorem oneParticleEmbedding_injective :
    Function.Injective (oneParticleEmbedding (Mode := Mode)) := by
  intro v w h
  ext i
  have hi := congrArg (fun ψ : FockSpace Mode => annihilate i ψ vacuum) h
  simpa [fockVacuum, basisState, Common.basisState] using hi

/-- The embedding is supported entirely on occupation configurations of total particle number one. -/
theorem oneParticleEmbedding_mem_supported (v : EuclideanSpace ℂ Mode) :
    oneParticleEmbedding v ∈
      Finsupp.supported ℂ ℂ {n : Occupation Mode | particleNumber n = 1} := by
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  exact Finsupp.single_mem_supported ℂ 1 (particleNumber_singleOccupation i)

/-- Second quantization restricts to the original operator on embedded one-boson states. -/
theorem secondQuantization_comp_oneParticleEmbedding
    (T : Module.End ℂ (EuclideanSpace ℂ Mode)) :
    (secondQuantization T).comp oneParticleEmbedding = oneParticleEmbedding.comp T := by
  apply (EuclideanSpace.basisFun Mode ℂ).toBasis.ext
  intro j
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
    LinearMap.comp_apply]
  rw [oneParticleEmbedding_single]
  simp [secondQuantization, oneParticleEmbedding, LinearMap.sum_apply,
    LinearMap.comp_apply, annihilate_basisState_singleOccupation, ite_smul]

end
end SecondQuantization.Bosonic
