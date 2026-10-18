import LeanCondensedMatter.Analysis.InfiniteSum.Order
import LeanCondensedMatter.Analysis.Inequalities.Gibbs
import LeanCondensedMatter.QuantumTheory.Gibbs.EigenbasisVariational

/-!
# Uniqueness for Gibbs energy-level distributions

This file characterizes equality in the countable diagonal Gibbs variational principle. Under the
same explicit energy-integrability hypothesis used for pure-point thermodynamics, the normalized
Gibbs probabilities define an admissible competitor. Equality in the Helmholtz lower bound holds
exactly for that competitor. Scalar and summable-family comparison helpers come from
`Analysis/Inequalities/Gibbs.lean`, without depending on bounded operator
equality machinery.
-/

noncomputable section

namespace QuantumTheory

variable {ι : Type*}

/-- The normalized pure-point Gibbs probabilities, bundled as an admissible variational competitor.
The explicit energy-integrability hypothesis is retained because state existence alone does not imply
finite mean energy. -/
noncomputable def eigenbasisGibbsCompetitor [Nonempty ι]
    (E : ι → ℝ) (β : ℝ) (hsum : EigenbasisGibbsSummable E β)
    (hint : EigenbasisGibbsEnergyIntegrable E β) :
    EigenbasisGibbsCompetitor E where
  probability := eigenbasisGibbsProbability E β
  nonneg := eigenbasisGibbsProbability_nonneg E β
  hasSum_one := hasSum_eigenbasisGibbsProbability E β hsum
  energyIntegrable := hint

/-- The canonical Gibbs competitor carries the normalized pure-point Gibbs probability. -/
@[simp]
theorem eigenbasisGibbsCompetitor_probability [Nonempty ι]
    (E : ι → ℝ) (β : ℝ) (hsum : EigenbasisGibbsSummable E β)
    (hint : EigenbasisGibbsEnergyIntegrable E β) (i : ι) :
    (eigenbasisGibbsCompetitor E β hsum hint).probability i =
      eigenbasisGibbsProbability E β i := rfl

private theorem eigenbasisGibbs_entropy_eq_iff
    [Nonempty ι] (E : ι → ℝ) (β : ℝ)
    (hsum : EigenbasisGibbsSummable E β) (p : EigenbasisGibbsCompetitor E) :
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
  have hbound : ∀ i, Real.negMulLog (p.probability i) ≤
      β * (p.probability i * E i) + p.probability i * Real.log Z -
        p.probability i + q i / Z := by
    intro i
    have hb := Real.negMulLog_le_of_neg_log_le
      (p := p.probability i) (q := q i) (Z := Z) (u := β * E i)
      (p.nonneg i) (eigenbasisBoltzmannWeight_pos E β i) hZpos (hlog i)
    nlinarith [hb]
  obtain ⟨hB, hBsumRaw⟩ :=
    Real.summable_gibbsComparison_and_tsum_eq
      p.probability q E β Z p.hasSum_one hEnergy hqsum
  have hqsum_le : ∑' i, q i ≤ Z := by
    rfl
  obtain ⟨hEntropySummable, _⟩ :=
    Real.summable_negMulLog_and_tsum_le_gibbs
      p.probability q E β Z p.nonneg p.hasSum_one hEnergy
      hqsum hqsum_le (fun i => eigenbasisBoltzmannWeight_pos E β i) hZpos hlog
  have hqZ : ∑' i, q i / Z = 1 := by
    rw [show (∑' i, q i / Z) = (∑' i, q i) / Z by
      rw [← tsum_div_const]]
    change eigenbasisPartitionFunction E β / Z = 1
    rw [show eigenbasisPartitionFunction E β = Z by rfl, div_self hZpos.ne']
  have hBsum :
      ∑' i, (β * (p.probability i * E i) + p.probability i * Real.log Z -
        p.probability i + q i / Z) =
        β * p.energy + Real.log Z := by
    calc
      ∑' i, (β * (p.probability i * E i) + p.probability i * Real.log Z -
          p.probability i + q i / Z) =
          β * (∑' i, p.probability i * E i) + Real.log Z - 1 + ∑' i, q i / Z :=
        hBsumRaw
      _ = β * p.energy + Real.log Z := by
        rw [hqZ]
        simp only [EigenbasisGibbsCompetitor.energy]
        ring
  constructor
  · intro heq
    have heqZ : p.entropy = β * p.energy + Real.log Z := by
      simpa [Z] using heq
    have hsum_eq :
        (∑' i, Real.negMulLog (p.probability i)) =
          ∑' i, (β * (p.probability i * E i) + p.probability i * Real.log Z -
            p.probability i + q i / Z) := by
      calc
        (∑' i, Real.negMulLog (p.probability i)) = p.entropy := rfl
        _ = β * p.energy + Real.log Z := heqZ
        _ = ∑' i, (β * (p.probability i * E i) + p.probability i * Real.log Z -
            p.probability i + q i / Z) := hBsum.symm
    have hterm_eq : ∀ i, Real.negMulLog (p.probability i) =
        β * (p.probability i * E i) + p.probability i * Real.log Z -
          p.probability i + q i / Z :=
      pointwise_eq_of_tsum_eq_of_le hbound hEntropySummable hB hsum_eq
    intro i
    have hqpos : 0 < q i := by
      simpa [q] using eigenbasisBoltzmannWeight_pos E β i
    have hqZpos : 0 < q i / Z := div_pos hqpos hZpos
    have henergylog :
        β * (p.probability i * E i) =
          -p.probability i * Real.log (q i) := by
      simp only [q, eigenbasisBoltzmannWeight, Real.log_exp]
      ring
    have hlogdiv : Real.log (q i / Z) = Real.log (q i) - Real.log Z :=
      Real.log_div hqpos.ne' hZpos.ne'
    have hscalar :
        Real.negMulLog (p.probability i) + p.probability i - q i / Z =
          -p.probability i * Real.log (q i / Z) := by
      have hterm := hterm_eq i
      rw [hlogdiv]
      rw [henergylog] at hterm
      nlinarith [hterm]
    have hpq :=
      (Real.gibbs_scalar_ineq_eq_iff (p.probability i) (q i / Z)
        (p.nonneg i) hqZpos).mp hscalar
    calc
      p.probability i = q i / Z := hpq
      _ = eigenbasisGibbsProbability E β i := by
        simp [q, Z, eigenbasisGibbsProbability, div_eq_mul_inv, mul_comm]
  · intro hp
    have hterm_eq : ∀ i, Real.negMulLog (p.probability i) =
        β * (p.probability i * E i) + p.probability i * Real.log Z -
          p.probability i + q i / Z := by
      intro i
      have hqpos : 0 < q i := by
        simpa [q] using eigenbasisBoltzmannWeight_pos E β i
      have hpq : p.probability i = q i / Z := by
        calc
          p.probability i = eigenbasisGibbsProbability E β i := hp i
          _ = q i / Z := by
            simp [q, Z, eigenbasisGibbsProbability, div_eq_mul_inv, mul_comm]
      rw [hpq, Real.negMulLog, Real.log_div hqpos.ne' hZpos.ne']
      simp only [q, eigenbasisBoltzmannWeight, Real.log_exp]
      ring
    calc
      p.entropy = ∑' i, Real.negMulLog (p.probability i) := rfl
      _ = ∑' i, (β * (p.probability i * E i) + p.probability i * Real.log Z -
          p.probability i + q i / Z) := tsum_congr hterm_eq
      _ = β * p.energy + Real.log Z := hBsum
      _ = β * p.energy + Real.log (eigenbasisPartitionFunction E β) := by rfl

/-- Equality in the countable pure-point Helmholtz lower bound holds exactly when the competitor
probabilities are the normalized Gibbs probabilities. -/
theorem eigenbasisGibbs_helmholtzFreeEnergy_eq_iff_probability_eq
    [Nonempty ι] (E : ι → ℝ) (β : ℝ) (hβ : 0 < β)
    (hsum : EigenbasisGibbsSummable E β) (p : EigenbasisGibbsCompetitor E) :
    p.helmholtzFreeEnergy β =
        -(1 / β) * Real.log (eigenbasisPartitionFunction E β) ↔
      ∀ i, p.probability i = eigenbasisGibbsProbability E β i := by
  have hβne : β ≠ 0 := ne_of_gt hβ
  have hcore := eigenbasisGibbs_entropy_eq_iff E β hsum p
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

/-- The Gibbs competitor attains the countable pure-point Helmholtz lower bound. -/
theorem eigenbasisGibbsCompetitor_helmholtzFreeEnergy_eq
    [Nonempty ι] (E : ι → ℝ) (β : ℝ) (hβ : 0 < β)
    (hsum : EigenbasisGibbsSummable E β)
    (hint : EigenbasisGibbsEnergyIntegrable E β) :
    (eigenbasisGibbsCompetitor E β hsum hint).helmholtzFreeEnergy β =
      -(1 / β) * Real.log (eigenbasisPartitionFunction E β) := by
  apply (eigenbasisGibbs_helmholtzFreeEnergy_eq_iff_probability_eq
    E β hβ hsum (eigenbasisGibbsCompetitor E β hsum hint)).2
  intro i
  rfl

/-- The admissible pure-point Gibbs competitor is the unique equality case of the countable
Helmholtz variational principle. -/
theorem eigenbasisGibbs_helmholtzFreeEnergy_eq_iff_eq_competitor
    [Nonempty ι] (E : ι → ℝ) (β : ℝ) (hβ : 0 < β)
    (hsum : EigenbasisGibbsSummable E β)
    (hint : EigenbasisGibbsEnergyIntegrable E β)
    (p : EigenbasisGibbsCompetitor E) :
    p.helmholtzFreeEnergy β =
        -(1 / β) * Real.log (eigenbasisPartitionFunction E β) ↔
      p = eigenbasisGibbsCompetitor E β hsum hint := by
  constructor
  · intro hfree
    have hprob : p.probability =
        (eigenbasisGibbsCompetitor E β hsum hint).probability := by
      funext i
      exact (eigenbasisGibbs_helmholtzFreeEnergy_eq_iff_probability_eq
        E β hβ hsum p).mp hfree i
    cases p
    cases hprob
    rfl
  · rintro rfl
    exact eigenbasisGibbsCompetitor_helmholtzFreeEnergy_eq E β hβ hsum hint

end QuantumTheory
