import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreePartitionFunction
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.OneBodyExpectation
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.BoundedEvolution
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.RankOneSecondQuantization
import LeanCondensedMatter.QuantumTheory.Gibbs.EigenbasisEntropy

set_option linter.style.header false

/-!
# Entropy of the finite free-fermion Gibbs state

The public entropy endpoint uses the generic finite pure-point Gibbs density state
at the explicit grand-canonical energy `K(n) = E(n) - μ N(n)`, not a fixed-`N`
canonical state or a new fermion-specific density constructor.
The generic identity `S = β ⟨K⟩ + log Ξ`, together with the finite fermionic
product factorization, reduces entropy to independent binary mode entropies.
The finite one-body expectation is evaluated using the explicit-`μ` grand-canonical
Gibbs state and finite-coordinate second quantization.
-/

namespace SecondQuantization
namespace Fermionic

open QuantumTheory

noncomputable section

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- File-local classical decidable equality, kept out of public theorem signatures. -/
local instance instDecidableEqFreeEntropy : DecidableEq Mode := Classical.decEq Mode

/-- The real Fermi–Dirac occupation of a single mode. -/
noncomputable def fermiDiracOccupation (ε : Mode → ℝ) (β : ℝ) (i : Mode) : ℝ :=
  (Real.exp (β * ε i) + 1)⁻¹

omit [LinearOrder Mode] in
private theorem eigenbasisPartitionFunction_fermionEnergy_eq_prod
    (ε : Mode → ℝ) (β : ℝ) :
    eigenbasisPartitionFunction (fermionEnergy ε) β =
      ∏ i, (1 + Real.exp (-β * ε i)) := by
  apply Complex.ofReal_injective
  have h := coe_grandCanonicalPartitionFunction_eq_prod ε β 0
  rw [Common.grandCanonicalPartitionFunction_eq_shifted] at h
  simp only [sub_zero] at h
  change ((eigenbasisPartitionFunction (fermionEnergy ε) β : ℝ) : ℂ) =
    ∏ i, (1 + Complex.exp (-(β : ℂ) * (ε i : ℂ))) at h
  push_cast [Complex.ofReal_exp]
  exact h

omit [LinearOrder Mode] in
private theorem log_eigenbasisPartitionFunction_fermionEnergy_eq_sum
    (ε : Mode → ℝ) (β : ℝ) :
    Real.log (eigenbasisPartitionFunction (fermionEnergy ε) β) =
      ∑ i, Real.log (1 + Real.exp (-β * ε i)) := by
  rw [eigenbasisPartitionFunction_fermionEnergy_eq_prod]
  simpa using
    (Real.log_prod
      (s := (Finset.univ : Finset Mode))
      (f := fun i => 1 + Real.exp (-β * ε i))
      (fun i _ => ne_of_gt (by positivity)))

omit [LinearOrder Mode] in
/-- The free-fermion Gibbs mean energy is the mode-energy sum weighted by Fermi–Dirac occupations. -/
theorem eigenbasisGibbsEnergyExpectation_fermionEnergy_eq_sum_fermiDirac
    (ε : Mode → ℝ) (β : ℝ) :
    eigenbasisGibbsEnergyExpectation (fermionEnergy ε) β =
      ∑ i, ε i * fermiDiracOccupation ε β i := by
  letI : LinearOrder Mode :=
    LinearOrder.lift' (Fintype.equivFin Mode) (Fintype.equivFin Mode).injective
  let D := Common.diagonalOperator (fun i => (ε i : ℂ))
  have h := finiteGrandCanonicalGibbsDensityOperator_expectation_finiteSecondQuantization ε β 0
    (Common.finiteHilbertOperatorAlgEquiv D)
  have hE : Common.grandCanonicalEnergy (Config := Occupation Mode) ε 0 =
      fermionEnergy ε := by
    funext n
    simpa using (Common.grandCanonicalEnergy_eq_shifted ε 0 n)
  rw [hE] at h
  simp only [sub_zero] at h
  have hquant : Lattice.finiteSecondQuantization (Common.finiteHilbertOperatorAlgEquiv D) =
      Lattice.boundedOneBodyOperator D := by
    simp [Lattice.finiteSecondQuantization]
  rw [hquant] at h
  simp only [AlgEquiv.symm_apply_apply] at h
  change Common.finiteGibbsExpectation (fermionEnergy ε) β
    (AlgebraicFock.occupationConjugate
      (Finsupp.basisSingleOne : Module.Basis Mode ℂ (Mode →₀ ℂ))
      (AlgebraicFock.dGamma ((Mode →₀ ℂ)) D)) = _ at h
  rw [Lattice.occupationConjugate_dGamma_diagonalOperator,
    Common.finiteGibbsExpectation_eq_sum] at h
  apply Complex.ofReal_injective
  rw [eigenbasisGibbsEnergyExpectation, tsum_fintype]
  push_cast [fermiDiracOccupation, Complex.ofReal_exp]
  simpa [D, Common.matrixCoeff_diagonalOperator, Common.diagonalOperator_apply,
    latticeKet, Finsupp.single_apply, fermionEnergy_eq_sum, div_eq_mul_inv] using h

omit [LinearOrder Mode] [Fintype Mode] in
private theorem fermiDiracOccupation_eq_exp_neg_div
    (ε : Mode → ℝ) (β : ℝ) (i : Mode) :
    fermiDiracOccupation ε β i =
      Real.exp (-β * ε i) / (1 + Real.exp (-β * ε i)) := by
  rw [fermiDiracOccupation, show -β * ε i = -(β * ε i) by ring, Real.exp_neg]
  field_simp [Real.exp_ne_zero]

omit [LinearOrder Mode] [Fintype Mode] in
private theorem one_sub_fermiDiracOccupation_eq_inv_one_add_exp_neg
    (ε : Mode → ℝ) (β : ℝ) (i : Mode) :
    1 - fermiDiracOccupation ε β i =
      (1 + Real.exp (-β * ε i))⁻¹ := by
  rw [fermiDiracOccupation, show -β * ε i = -(β * ε i) by ring, Real.exp_neg]
  field_simp [Real.exp_ne_zero]
  ring

omit [LinearOrder Mode] [Fintype Mode] in
private theorem binaryEntropy_fermiDiracOccupation
    (ε : Mode → ℝ) (β : ℝ) (i : Mode) :
    Real.negMulLog (fermiDiracOccupation ε β i) +
        Real.negMulLog (1 - fermiDiracOccupation ε β i) =
      (β * ε i) * fermiDiracOccupation ε β i +
        Real.log (1 + Real.exp (-β * ε i)) := by
  have hqpos : 0 < Real.exp (-β * ε i) := Real.exp_pos _
  have hdenpos : 0 < 1 + Real.exp (-β * ε i) := by positivity
  have hlogf :
      Real.log (fermiDiracOccupation ε β i) =
        -β * ε i - Real.log (1 + Real.exp (-β * ε i)) := by
    rw [fermiDiracOccupation_eq_exp_neg_div ε β i,
      Real.log_div hqpos.ne' hdenpos.ne', Real.log_exp]
  have hlog1mf :
      Real.log (1 - fermiDiracOccupation ε β i) =
        -Real.log (1 + Real.exp (-β * ε i)) := by
    rw [one_sub_fermiDiracOccupation_eq_inv_one_add_exp_neg ε β i,
      Real.log_inv]
  rw [Real.negMulLog, Real.negMulLog, hlogf, hlog1mf]
  ring

omit [LinearOrder Mode] in
/-- The full-occupation-space finite fermionic grand-canonical Gibbs entropy is the
sum of binary entropies for occupations at the effective energy `ε - μ`.
This uses the generic pure-point Gibbs density state directly, without a second finite
fermionic density constructor. It does not assert a fixed-particle-number canonical entropy. -/
theorem vonNeumannEntropy_finiteGrandCanonicalGibbs_toReal_eq_sum_fermiDirac
    (ε : Mode → ℝ) (β μ : ℝ) :
    (vonNeumannEntropy
      (eigenbasisGibbsDensityOperator
        (Common.finiteHilbertBasis (Config := Occupation Mode))
        (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β
        (eigenbasisGibbsSummable_of_finite
          (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β))).toReal =
      ∑ i, (Real.negMulLog (fermiDiracOccupation (fun j => ε j - μ) β i) +
        Real.negMulLog (1 - fermiDiracOccupation (fun j => ε j - μ) β i)) := by
  let ξ : Mode → ℝ := fun i => ε i - μ
  have hE : Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ =
      fermionEnergy ξ := by
    funext n
    exact Common.grandCanonicalEnergy_eq_shifted ε μ n
  rw [hE]
  have hIntegrable : EigenbasisGibbsEnergyIntegrable (fermionEnergy ξ) β :=
    Summable.of_finite
  rw [(vonNeumannEntropy_eigenbasisGibbsDensityOperator
    (Common.finiteHilbertBasis (Config := Occupation Mode))
    (fermionEnergy ξ) β
    (eigenbasisGibbsSummable_of_finite (fermionEnergy ξ) β) hIntegrable).2,
    eigenbasisGibbsEnergyExpectation_fermionEnergy_eq_sum_fermiDirac,
    log_eigenbasisPartitionFunction_fermionEnergy_eq_sum]
  calc
    β * (∑ i, ξ i * fermiDiracOccupation ξ β i) +
        ∑ i, Real.log (1 + Real.exp (-β * ξ i)) =
      ∑ i, ((β * ξ i) * fermiDiracOccupation ξ β i +
        Real.log (1 + Real.exp (-β * ξ i))) := by
      rw [Finset.mul_sum, Finset.sum_add_distrib]
      ring_nf
    _ = ∑ i, (Real.negMulLog (fermiDiracOccupation ξ β i) +
        Real.negMulLog (1 - fermiDiracOccupation ξ β i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (binaryEntropy_fermiDiracOccupation ξ β i).symm

end
end Fermionic
end SecondQuantization
