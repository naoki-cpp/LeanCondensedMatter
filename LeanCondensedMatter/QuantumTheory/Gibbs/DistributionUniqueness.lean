import LeanCondensedMatter.Analysis.Inequalities.Gibbs
import LeanCondensedMatter.QuantumTheory.Gibbs.DistributionVariational

/-!
# Equality and uniqueness in the Gibbs distribution variational principle

This file characterizes equality in the countable diagonal Gibbs variational principle. Under the
same explicit energy-integrability hypothesis used for energy-level thermodynamics, the normalized
Gibbs probabilities define an admissible competitor. Equality in the Helmholtz lower bound holds
exactly for that competitor. Scalar and summable-family comparison helpers come from
`Analysis/Inequalities/Gibbs.lean`, without depending on bounded operator
equality machinery.
-/

noncomputable section

namespace QuantumTheory

variable {ι : Type*}

/-- The normalized energy-level Gibbs probabilities, bundled as an admissible variational competitor.
The explicit energy-integrability hypothesis is retained because state existence alone does not imply
finite mean energy. -/
noncomputable def gibbsEquilibriumDistribution [Nonempty ι]
    (E : ι → ℝ) (β : ℝ) (hsum : EigenbasisGibbsSummable E β)
    (hint : EigenbasisGibbsEnergyIntegrable E β) :
    GibbsVariationalDistribution E where
  probability := eigenbasisGibbsProbability E β
  nonneg := eigenbasisGibbsProbability_nonneg E β
  hasSum_one := hasSum_eigenbasisGibbsProbability E β hsum
  energyIntegrable := hint

/-- The normalized Gibbs equilibrium competitor carries the energy-level Gibbs probability. -/
@[simp]
theorem gibbsEquilibriumDistribution_probability [Nonempty ι]
    (E : ι → ℝ) (β : ℝ) (hsum : EigenbasisGibbsSummable E β)
    (hint : EigenbasisGibbsEnergyIntegrable E β) (i : ι) :
    (gibbsEquilibriumDistribution E β hsum hint).probability i =
      eigenbasisGibbsProbability E β i := rfl

private theorem gibbsVariational_entropy_eq_iff
    [Nonempty ι] (E : ι → ℝ) (β : ℝ)
    (hsum : EigenbasisGibbsSummable E β) (p : GibbsVariationalDistribution E) :
    p.entropy = β * p.energy + Real.log (eigenbasisPartitionFunction E β) ↔
      ∀ i, p.probability i = eigenbasisGibbsProbability E β i := by
  let Z := eigenbasisPartitionFunction E β
  let q := eigenbasisBoltzmannWeight E β
  have hZpos : 0 < Z := by
    simpa [Z] using eigenbasisPartitionFunction_pos E β hsum
  have hqsum : Summable q := by
    simpa [q] using eigenbasisBoltzmannWeight_summable E β hsum
  have hEnergy : Summable fun i => p.probability i * E i :=
    Summable.of_norm p.energyIntegrable
  have hlog : ∀ i, -Real.log (q i) ≤ β * E i := by
    intro i
    have hlogEq : -Real.log (q i) = β * E i := by
      simp [q, eigenbasisBoltzmannWeight]
    exact hlogEq.le
  have hcore := Real.tsum_negMulLog_eq_gibbs_iff
    p.probability q E β Z p.nonneg p.hasSum_one hEnergy hqsum (by rfl)
    (fun i => eigenbasisBoltzmannWeight_pos E β i) hZpos hlog
  change (∑' i, Real.negMulLog (p.probability i)) =
      β * (∑' i, p.probability i * E i) + Real.log Z ↔ _
  rw [hcore]
  constructor
  · rintro ⟨_, hterm⟩ i
    simpa [q, Z, eigenbasisGibbsProbability, div_eq_mul_inv, mul_comm] using (hterm i).1
  · intro hp
    refine ⟨rfl, fun i => ⟨?_, ?_⟩⟩
    · simpa [q, Z, eigenbasisGibbsProbability, div_eq_mul_inv, mul_comm] using hp i
    · simp [q, eigenbasisBoltzmannWeight]

/-- Equality in the countable energy-level Helmholtz lower bound holds exactly when the competitor
probabilities are the normalized Gibbs probabilities. -/
theorem gibbsVariational_helmholtzFreeEnergy_eq_iff_probability_eq
    [Nonempty ι] (E : ι → ℝ) (β : ℝ) (hβ : 0 < β)
    (hsum : EigenbasisGibbsSummable E β) (p : GibbsVariationalDistribution E) :
    p.helmholtzFreeEnergy β =
        -(1 / β) * Real.log (eigenbasisPartitionFunction E β) ↔
      ∀ i, p.probability i = eigenbasisGibbsProbability E β i := by
  have hβne : β ≠ 0 := ne_of_gt hβ
  have hcore := gibbsVariational_entropy_eq_iff E β hsum p
  constructor
  · intro hfree
    apply hcore.mp
    have hfree' := hfree
    change p.energy - (1 / β) * p.entropy =
      -(1 / β) * Real.log (eigenbasisPartitionFunction E β) at hfree'
    field_simp [hβne] at hfree'
    linarith
  · intro hp
    have hentropy := hcore.mpr hp
    change p.energy - (1 / β) * p.entropy =
      -(1 / β) * Real.log (eigenbasisPartitionFunction E β)
    field_simp [hβne]
    linarith

/-- The Gibbs competitor attains the countable energy-level Helmholtz lower bound. -/
theorem gibbsEquilibriumDistribution_helmholtzFreeEnergy_eq
    [Nonempty ι] (E : ι → ℝ) (β : ℝ) (hβ : 0 < β)
    (hsum : EigenbasisGibbsSummable E β)
    (hint : EigenbasisGibbsEnergyIntegrable E β) :
    (gibbsEquilibriumDistribution E β hsum hint).helmholtzFreeEnergy β =
      -(1 / β) * Real.log (eigenbasisPartitionFunction E β) := by
  apply (gibbsVariational_helmholtzFreeEnergy_eq_iff_probability_eq
    E β hβ hsum (gibbsEquilibriumDistribution E β hsum hint)).2
  intro i
  rfl

/-- The equilibrium Gibbs distribution is the unique equality case of the countable
Helmholtz variational principle. -/
theorem gibbsVariational_helmholtzFreeEnergy_eq_iff_eq_equilibrium
    [Nonempty ι] (E : ι → ℝ) (β : ℝ) (hβ : 0 < β)
    (hsum : EigenbasisGibbsSummable E β)
    (hint : EigenbasisGibbsEnergyIntegrable E β)
    (p : GibbsVariationalDistribution E) :
    p.helmholtzFreeEnergy β =
        -(1 / β) * Real.log (eigenbasisPartitionFunction E β) ↔
      p = gibbsEquilibriumDistribution E β hsum hint := by
  constructor
  · intro hfree
    have hprob : p.probability =
        (gibbsEquilibriumDistribution E β hsum hint).probability := by
      funext i
      exact (gibbsVariational_helmholtzFreeEnergy_eq_iff_probability_eq
        E β hβ hsum p).mp hfree i
    cases p
    cases hprob
    rfl
  · rintro rfl
    exact gibbsEquilibriumDistribution_helmholtzFreeEnergy_eq E β hβ hsum hint

end QuantumTheory
