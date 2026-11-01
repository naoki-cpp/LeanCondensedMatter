import LeanCondensedMatter.Analysis.Inequalities.Gibbs
import LeanCondensedMatter.QuantumTheory.Gibbs.FreeEnergy
import LeanCondensedMatter.Analysis.Inequalities.PeierlsBogoliubovEquality

/-!
# Equality components of the Gibbs variational bound

The equality case of the Gibbs–Klein free-energy bound determines the diagonal Gibbs weights,
saturation of the Gibbs trace, and equality in the Peierls–Bogoliubov inequality. Scalar and
summable-family equality conditions are supplied by `Analysis.Inequalities.Gibbs`.
-/

namespace QuantumTheory

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- For nonzero inverse temperature, equality in the Helmholtz bound forces the three equality
components needed for uniqueness: the Gibbs diagonal sum saturates the trace, every density
eigenvalue equals the normalized Gibbs diagonal weight, and every Peierls–Bogoliubov bound is
saturated. -/
theorem helmholtzFreeEnergy_eq_components [Nontrivial H] [FiniteDimensional ℂ H]
    (ρ : DensityOperator H) (Hop : Observable H) (β : ℝ) (hβ : β ≠ 0)
    (hfree : energyExpValue ρ Hop -
        (1 / β) * (vonNeumannEntropy ρ).toReal =
      -(1 / β) * Real.log (spectralTrace (gibbsOp Hop β))) :
    (∑' a : EigenvectorIndex ρ.op,
        diagonalExpectationValue (gibbsOp Hop β)
          (gibbsOp_isPositive Hop β).isSelfAdjoint
          (eigenvectorFamily ρ.spectralTraceClass.compact a)) =
        spectralTrace (gibbsOp Hop β) ∧
      (∀ a : EigenvectorIndex ρ.op,
        a.1.1 =
          diagonalExpectationValue (gibbsOp Hop β)
            (gibbsOp_isPositive Hop β).isSelfAdjoint
            (eigenvectorFamily ρ.spectralTraceClass.compact a) /
              spectralTrace (gibbsOp Hop β)) ∧
      (∀ a : EigenvectorIndex ρ.op,
        Real.exp (-β * diagonalExpectationValue Hop.1 Hop.2
          (eigenvectorFamily ρ.spectralTraceClass.compact a)) =
          diagonalExpectationValue (gibbsOp Hop β)
            (gibbsOp_isPositive Hop β).isSelfAdjoint
            (eigenvectorFamily ρ.spectralTraceClass.compact a)) := by
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
  have hph_hasSum := hasSum_eigenvalue_mul_energy ρ Hop
  have hq_summable_and_le : Summable q ∧ ∑' a, q a ≤ Z := by
    have hbound := hGibbs.sum_diagonalExpectationValue_le_spectralTrace
      (gibbsOp_isPositive Hop β).toLinearMap hd_orth
    simpa [Z, hq_def] using hbound
  obtain ⟨hnML_summable, _⟩ :=
    Real.summable_negMulLog_and_tsum_le_gibbs
      p q h β Z (fun a => ρ.eigenvalue_nonneg a)
      hp_hasSum hph_hasSum.summable
      hq_summable_and_le.1 hq_summable_and_le.2 hqpos hZpos hstep2
  obtain ⟨-, hToReal⟩ :=
    vonNeumannEntropy_ne_top_and_toReal_eq_tsum ρ hnML_summable
  have hEntropyTarget :
      (vonNeumannEntropy ρ).toReal = β * energyExpValue ρ Hop + Real.log Z := by
    have hfree' := hfree
    change energyExpValue ρ Hop - (1 / β) * (vonNeumannEntropy ρ).toReal =
      -(1 / β) * Real.log Z at hfree'
    field_simp [hβ] at hfree'
    linarith
  have hnMLTarget :
      ∑' a, Real.negMulLog (p a) = β * energyExpValue ρ Hop + Real.log Z := by
    rw [← hToReal]
    exact hEntropyTarget
  have hequality := (Real.tsum_negMulLog_eq_gibbs_iff
    p q h β Z (fun a => ρ.eigenvalue_nonneg a) hp_hasSum hph_hasSum.summable
    hq_summable_and_le.1 hq_summable_and_le.2 hqpos hZpos hstep2).mp
      (by rw [hph_hasSum.tsum_eq]; exact hnMLTarget)
  obtain ⟨hqsum_eq, hscalar⟩ := hequality
  have hpeierls : ∀ a, Real.exp (-β * h a) = q a := fun a => by
    have hlogeq : Real.log (q a) = -β * h a := by
      linarith [(hscalar a).2]
    calc
      Real.exp (-β * h a) = Real.exp (Real.log (q a)) := by rw [hlogeq]
      _ = q a := Real.exp_log (hqpos a)
  refine ⟨?_, ?_, ?_⟩
  · simpa [d, q, Z] using hqsum_eq
  · intro a
    simpa [p, q, Z, d] using (hscalar a).1
  · intro a
    simpa [h, q, d] using hpeierls a

end QuantumTheory
