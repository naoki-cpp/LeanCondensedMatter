import LeanCondensedMatter.Analysis.Inequalities.Gibbs
import LeanCondensedMatter.QuantumTheory.Gibbs.EnergyExpectation
import LeanCondensedMatter.QuantumTheory.Gibbs.State
import LeanCondensedMatter.QuantumTheory.Entropy.Basic
import LeanCondensedMatter.Analysis.Inequalities.PeierlsBogoliubov
import LeanCondensedMatter.Analysis.InfiniteSum.Order
import LeanCondensedMatter.Analysis.Operator.TraceClass.Spectral.Bundled

/-!
# Helmholtz free-energy inequality

For any density operator, bounded Hamiltonian, and positive inverse temperature, the Helmholtz free
energy is bounded below by the free energy determined by the spectral trace of `e^{-βH}`.
-/

namespace QuantumTheory

open ContinuousLinearMap
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The spectral trace of a finite-dimensional Gibbs operator is strictly positive. -/
theorem spectralTrace_gibbsOp_pos [Nontrivial H] [FiniteDimensional ℂ H]
    (Hop : Observable H) (β : ℝ) :
    0 < spectralTrace (gibbsOp Hop β) := by
  let htrace := gibbsOp_spectralTraceClass Hop β
  exact htrace.spectralTrace_pos (gibbsOp_isPositive Hop β) (gibbsOp_ne_zero Hop β)

/-- Peierls–Bogoliubov in lossless diagonal-expectation form against a unit vector. -/
theorem exp_neg_beta_energy_le_gibbs_diagonal (Hop : Observable H) (β : ℝ) (v : H)
    (hv : ‖v‖ = 1) :
    Real.exp (-β * diagonalExpectationValue Hop.1 Hop.2 v) ≤
      diagonalExpectationValue (gibbsOp Hop β) (gibbsOp_isPositive Hop β).isSelfAdjoint v := by
  have hpb := gibbs_peierls_bogoliubov Hop.1 Hop.2 β v hv
  change (Real.exp (-β * diagonalExpectationValue Hop.1 Hop.2 v) : ℂ) ≤
    inner ℂ (gibbsOp Hop β v) v at hpb
  rw [← coe_diagonalExpectationValue
    (gibbsOp Hop β) (gibbsOp_isPositive Hop β).isSelfAdjoint v] at hpb
  exact_mod_cast hpb

/-- The eigenvalue-weighted lossless energy-expectation sum is summable, with total
`energyExpValue ρ Hop`. -/
theorem summable_eigenvalue_mul_energy_and_tsum (ρ : DensityOperator H) (Hop : Observable H) :
    Summable (fun a : EigenvectorIndex ρ.op =>
        a.1.1 * diagonalExpectationValue Hop.1 Hop.2
          (eigenvectorFamily ρ.spectralTraceClass.compact a)) ∧
      ∑' a : EigenvectorIndex ρ.op,
          a.1.1 * diagonalExpectationValue Hop.1 Hop.2
            (eigenvectorFamily ρ.spectralTraceClass.compact a) =
        energyExpValue ρ Hop := by
  have hsComplex : HasSum
      (fun a : EigenvectorIndex ρ.op =>
        ((a.1.1 * diagonalExpectationValue Hop.1 Hop.2
          (eigenvectorFamily ρ.spectralTraceClass.compact a) : ℝ) : ℂ))
      (energyExpValue ρ Hop : ℂ) := by
    have hs := (ρ.summable_expectation_term Hop.1).hasSum
    rw [← ρ.expectation_eq_spectral_tsum Hop.1, ρ.expectation_observable] at hs
    simpa only [Complex.ofReal_mul, coe_diagonalExpectationValue_right, energyExpValue] using hs
  have hsReal : HasSum
      (fun a : EigenvectorIndex ρ.op =>
        a.1.1 * diagonalExpectationValue Hop.1 Hop.2
          (eigenvectorFamily ρ.spectralTraceClass.compact a))
      (energyExpValue ρ Hop) := by
    exact_mod_cast hsComplex
  exact ⟨hsReal.summable, hsReal.tsum_eq⟩

/-- The Gibbs–Klein / Helmholtz free-energy inequality. -/
theorem helmholtzFreeEnergy_ge_and_entropy_ne_top [Nontrivial H] [FiniteDimensional ℂ H]
    (ρ : DensityOperator H) (Hop : Observable H)
    (β : ℝ) (hβ : 0 < β) :
    vonNeumannEntropy ρ ≠ ⊤ ∧
      -(1 / β) * Real.log (spectralTrace (gibbsOp Hop β)) ≤
        energyExpValue ρ Hop - (1 / β) * (vonNeumannEntropy ρ).toReal := by
  set d := eigenvectorFamily ρ.spectralTraceClass.compact with hd_def
  set p : EigenvectorIndex ρ.op → ℝ := fun a => a.1.1 with hp_def
  set h : EigenvectorIndex ρ.op → ℝ :=
    fun a => diagonalExpectationValue Hop.1 Hop.2 (d a) with hh_def
  set q : EigenvectorIndex ρ.op → ℝ := fun a =>
    diagonalExpectationValue (gibbsOp Hop β)
      (gibbsOp_isPositive Hop β).isSelfAdjoint (d a) with hq_def
  set Z : ℝ := spectralTrace (gibbsOp Hop β) with hZ_def
  have hZpos : 0 < Z := spectralTrace_gibbsOp_pos Hop β
  have hd_orth : Orthonormal ℂ d :=
    orthonormal_eigenvectorFamily ρ.spectralTraceClass.compact ρ.isSymmetric
  have hd_unit : ∀ a, ‖d a‖ = 1 := eigenvectorFamily_norm_eq_one ρ
  let hGibbs : SpectralTraceClass (gibbsOp Hop β) :=
    gibbsOp_spectralTraceClass Hop β
  have hstep1 : ∀ a, Real.exp (-β * h a) ≤ q a := fun a => by
    simpa [hh_def, hq_def] using
      exp_neg_beta_energy_le_gibbs_diagonal Hop β (d a) (hd_unit a)
  have hqpos : ∀ a, 0 < q a := fun a => (Real.exp_pos _).trans_le (hstep1 a)
  have hstep2 : ∀ a, -Real.log (q a) ≤ β * h a := fun a =>
    Real.neg_log_le_of_exp_le (u := β * h a) (by rw [← neg_mul]; exact hstep1 a)
  have hp_hasSum : HasSum p 1 := by
    simpa [p] using ρ.hasSum_eigenvalues_eq_one
  obtain ⟨hph_summable, hphsum⟩ := summable_eigenvalue_mul_energy_and_tsum ρ Hop
  have hq_summable_and_le : Summable q ∧ ∑' a, q a ≤ Z := by
    have hbound := hGibbs.sum_diagonalExpectationValue_le_spectralTrace
      (gibbsOp_isPositive Hop β).toLinearMap hd_orth
    simpa [Z, hq_def] using hbound
  obtain ⟨hnML_summable, hfinal⟩ :=
    Real.summable_negMulLog_and_tsum_le_gibbs
      p q h β Z (fun a => ρ.eigenvalue_nonneg a)
      hp_hasSum hph_summable
      hq_summable_and_le.1 hq_summable_and_le.2 hqpos hZpos hstep2
  obtain ⟨hEntropyNeTop, hToReal⟩ :=
    vonNeumannEntropy_ne_top_and_toReal_eq_tsum ρ hnML_summable
  rw [hphsum] at hfinal
  refine ⟨hEntropyNeTop, ?_⟩
  rw [hToReal]
  have hβinv : 0 < 1 / β := by positivity
  have hcancel : (1 / β) * (β * energyExpValue ρ Hop) = energyExpValue ρ Hop := by
    field_simp
  have hmul := mul_le_mul_of_nonneg_left hfinal hβinv.le
  rw [mul_add, hcancel] at hmul
  linarith [hmul]

end QuantumTheory
