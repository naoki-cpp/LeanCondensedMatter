import LeanCondensedMatter.QuantumTheory.Gibbs.PurePointVariational
import LeanCondensedMatter.QuantumTheory.Gibbs.Equality

/-!
# Uniqueness for countable pure-point Gibbs competitors

This file characterizes equality in the countable diagonal Gibbs variational principle. Under the
same explicit energy-integrability hypothesis used for pure-point thermodynamics, the normalized
Gibbs probabilities define an admissible competitor. Equality in the Helmholtz lower bound holds
exactly for that competitor.
-/

noncomputable section

namespace QuantumTheory

variable {ι : Type*}

/-- The normalized pure-point Gibbs probabilities, bundled as an admissible variational competitor.
The explicit energy-integrability hypothesis is retained because state existence alone does not imply
finite mean energy. -/
noncomputable def purePointGibbsCompetitor [Nonempty ι]
    (E : ι → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable E β)
    (hint : PurePointGibbsEnergyIntegrable E β) :
    PurePointGibbsCompetitor E where
  probability := purePointGibbsProbability E β
  nonneg := purePointGibbsProbability_nonneg E β hsum
  hasSum_one := hasSum_purePointGibbsProbability E β hsum
  entropySummable :=
    Summable.of_norm (summable_norm_negMulLog_purePointGibbsProbability E β hsum hint)
  energyIntegrable := hint

@[simp]
theorem purePointGibbsCompetitor_probability [Nonempty ι]
    (E : ι → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable E β)
    (hint : PurePointGibbsEnergyIntegrable E β) (i : ι) :
    (purePointGibbsCompetitor E β hsum hint).probability i =
      purePointGibbsProbability E β i := rfl

private theorem purePointGibbsCompetitor_eq_of_probability_eq
    {E : ι → ℝ} {p q : PurePointGibbsCompetitor E}
    (h : p.probability = q.probability) : p = q := by
  cases p
  cases q
  cases h
  rfl

private theorem purePointGibbs_entropy_le_and_eq_iff
    [Nonempty ι] (E : ι → ℝ) (β : ℝ)
    (hsum : PurePointGibbsSummable E β) (p : PurePointGibbsCompetitor E) :
    p.entropy ≤ β * p.energy + Real.log (purePointPartitionFunction E β) ∧
      (p.entropy = β * p.energy + Real.log (purePointPartitionFunction E β) ↔
        ∀ i, p.probability i = purePointGibbsProbability E β i) := by
  let Z := purePointPartitionFunction E β
  let q := purePointBoltzmannWeight E β
  have hZpos : 0 < Z := by
    simpa [Z] using purePointPartitionFunction_pos E β hsum
  have hqsum : Summable q := by
    simpa [q] using purePointBoltzmannWeight_summable E β hsum
  have hEnergy : Summable fun i => p.probability i * E i :=
    Summable.of_norm p.energyIntegrable
  have hB : Summable fun i =>
      β * (p.probability i * E i) + p.probability i * Real.log Z -
        p.probability i + q i / Z :=
    (((hEnergy.mul_left β).add (p.hasSum_one.summable.mul_right (Real.log Z))).sub
      p.hasSum_one.summable).add (hqsum.div_const Z)
  have hbound : ∀ i, Real.negMulLog (p.probability i) ≤
      β * (p.probability i * E i) + p.probability i * Real.log Z -
        p.probability i + q i / Z := by
    intro i
    have hlog : -Real.log (q i) = β * E i := by
      simp [q, purePointBoltzmannWeight]
    have hb := negMulLog_le_of_neg_log_le
      (p := p.probability i) (q := q i) (Z := Z) (u := β * E i)
      (p.nonneg i) (purePointBoltzmannWeight_pos E β i) hZpos hlog.le
    nlinarith [hb]
  have hsum_le := p.entropySummable.tsum_le_tsum hbound hB
  have hqZ : ∑' i, q i / Z = 1 := by
    rw [show (∑' i, q i / Z) = (∑' i, q i) / Z by
      rw [← tsum_div_const]]
    change purePointPartitionFunction E β / Z = 1
    rw [show purePointPartitionFunction E β = Z by rfl, div_self hZpos.ne']
  have hBsum :
      ∑' i, (β * (p.probability i * E i) + p.probability i * Real.log Z -
        p.probability i + q i / Z) =
        β * p.energy + Real.log Z := by
    rw [(((hEnergy.mul_left β).add (p.hasSum_one.summable.mul_right (Real.log Z))).sub
      p.hasSum_one.summable).tsum_add (hqsum.div_const Z),
      ((hEnergy.mul_left β).add
        (p.hasSum_one.summable.mul_right (Real.log Z))).tsum_sub p.hasSum_one.summable,
      (hEnergy.mul_left β).tsum_add
        (p.hasSum_one.summable.mul_right (Real.log Z)),
      tsum_mul_left, tsum_mul_right, p.hasSum_one.tsum_eq, hqZ]
    simp only [PurePointGibbsCompetitor.energy]
    ring
  have hmain : p.entropy ≤ β * p.energy + Real.log Z := by
    rw [PurePointGibbsCompetitor.entropy, ← hBsum]
    exact hsum_le
  refine ⟨by simpa [Z] using hmain, ?_⟩
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
          p.probability i + q i / Z := by
      intro i
      apply le_antisymm (hbound i)
      by_contra hnot
      have hlt : Real.negMulLog (p.probability i) <
          β * (p.probability i * E i) + p.probability i * Real.log Z -
            p.probability i + q i / Z :=
        lt_of_not_ge hnot
      have hsumlt :=
        Summable.tsum_lt_tsum hbound hlt p.entropySummable hB
      exact (ne_of_lt hsumlt) hsum_eq
    intro i
    have hqpos : 0 < q i := by
      simpa [q] using purePointBoltzmannWeight_pos E β i
    have hqZpos : 0 < q i / Z := div_pos hqpos hZpos
    have hlog : -Real.log (q i) = β * E i := by
      simp [q, purePointBoltzmannWeight]
    have henergylog :
        β * (p.probability i * E i) =
          -p.probability i * Real.log (q i) := by
      calc
        β * (p.probability i * E i) =
            p.probability i * (β * E i) := by ring
        _ = p.probability i * (-Real.log (q i)) := by rw [← hlog]
        _ = -p.probability i * Real.log (q i) := by ring
    have hlogdiv : Real.log (q i / Z) = Real.log (q i) - Real.log Z :=
      Real.log_div hqpos.ne' hZpos.ne'
    have hscalar :
        Real.negMulLog (p.probability i) + p.probability i - q i / Z =
          -p.probability i * Real.log (q i / Z) := by
      rw [hlogdiv]
      rw [henergylog] at hterm_eq
      nlinarith [hterm_eq i]
    have hpq :=
      (gibbs_scalar_ineq_eq_iff (p.probability i) (q i / Z)
        (p.nonneg i) hqZpos).mp hscalar
    calc
      p.probability i = q i / Z := hpq
      _ = purePointGibbsProbability E β i := by
        simp [q, Z, purePointGibbsProbability, div_eq_mul_inv, mul_comm]
  · intro hp
    have hterm_eq : ∀ i, Real.negMulLog (p.probability i) =
        β * (p.probability i * E i) + p.probability i * Real.log Z -
          p.probability i + q i / Z := by
      intro i
      have hqpos : 0 < q i := by
        simpa [q] using purePointBoltzmannWeight_pos E β i
      have hqZpos : 0 < q i / Z := div_pos hqpos hZpos
      have hpq : p.probability i = q i / Z := by
        calc
          p.probability i = purePointGibbsProbability E β i := hp i
          _ = q i / Z := by
            simp [q, Z, purePointGibbsProbability, div_eq_mul_inv, mul_comm]
      have hscalar :=
        (gibbs_scalar_ineq_eq_iff (p.probability i) (q i / Z)
          (p.nonneg i) hqZpos).mpr hpq
      have hlog : -Real.log (q i) = β * E i := by
        simp [q, purePointBoltzmannWeight]
      have henergylog :
          β * (p.probability i * E i) =
            -p.probability i * Real.log (q i) := by
        calc
          β * (p.probability i * E i) =
              p.probability i * (β * E i) := by ring
          _ = p.probability i * (-Real.log (q i)) := by rw [← hlog]
          _ = -p.probability i * Real.log (q i) := by ring
      have hlogdiv : Real.log (q i / Z) = Real.log (q i) - Real.log Z :=
        Real.log_div hqpos.ne' hZpos.ne'
      rw [hlogdiv] at hscalar
      nlinarith [hscalar, henergylog]
    calc
      p.entropy = ∑' i, Real.negMulLog (p.probability i) := rfl
      _ = ∑' i, (β * (p.probability i * E i) + p.probability i * Real.log Z -
          p.probability i + q i / Z) := tsum_congr hterm_eq
      _ = β * p.energy + Real.log Z := hBsum
      _ = β * p.energy + Real.log (purePointPartitionFunction E β) := by rfl

/-- Equality in the countable pure-point Helmholtz lower bound holds exactly when the competitor
probabilities are the normalized Gibbs probabilities. -/
theorem purePointGibbs_helmholtzFreeEnergy_eq_iff_probability_eq
    [Nonempty ι] (E : ι → ℝ) (β : ℝ) (hβ : 0 < β)
    (hsum : PurePointGibbsSummable E β) (p : PurePointGibbsCompetitor E) :
    p.helmholtzFreeEnergy β =
        -(1 / β) * Real.log (purePointPartitionFunction E β) ↔
      ∀ i, p.probability i = purePointGibbsProbability E β i := by
  have hβne : β ≠ 0 := ne_of_gt hβ
  have hcore := (purePointGibbs_entropy_le_and_eq_iff E β hsum p).2
  constructor
  · intro hfree
    apply hcore.mp
    have hfree' := hfree
    change p.energy - (1 / β) * p.entropy =
      -(1 / β) * Real.log (purePointPartitionFunction E β) at hfree'
    field_simp [hβne] at hfree'
    linarith
  · intro hp
    have hentropy := hcore.mpr hp
    change p.energy - (1 / β) * p.entropy =
      -(1 / β) * Real.log (purePointPartitionFunction E β)
    field_simp [hβne]
    linarith

/-- The Gibbs competitor attains the countable pure-point Helmholtz lower bound. -/
theorem purePointGibbsCompetitor_helmholtzFreeEnergy_eq
    [Nonempty ι] (E : ι → ℝ) (β : ℝ) (hβ : 0 < β)
    (hsum : PurePointGibbsSummable E β)
    (hint : PurePointGibbsEnergyIntegrable E β) :
    (purePointGibbsCompetitor E β hsum hint).helmholtzFreeEnergy β =
      -(1 / β) * Real.log (purePointPartitionFunction E β) := by
  apply (purePointGibbs_helmholtzFreeEnergy_eq_iff_probability_eq
    E β hβ hsum (purePointGibbsCompetitor E β hsum hint)).2
  intro i
  rfl

/-- The admissible pure-point Gibbs competitor is the unique equality case of the countable
Helmholtz variational principle. -/
theorem purePointGibbs_helmholtzFreeEnergy_eq_iff_eq_competitor
    [Nonempty ι] (E : ι → ℝ) (β : ℝ) (hβ : 0 < β)
    (hsum : PurePointGibbsSummable E β)
    (hint : PurePointGibbsEnergyIntegrable E β)
    (p : PurePointGibbsCompetitor E) :
    p.helmholtzFreeEnergy β =
        -(1 / β) * Real.log (purePointPartitionFunction E β) ↔
      p = purePointGibbsCompetitor E β hsum hint := by
  constructor
  · intro hfree
    apply purePointGibbsCompetitor_eq_of_probability_eq
    funext i
    exact (purePointGibbs_helmholtzFreeEnergy_eq_iff_probability_eq
      E β hβ hsum p).mp hfree i
  · rintro rfl
    exact purePointGibbsCompetitor_helmholtzFreeEnergy_eq E β hβ hsum hint

end QuantumTheory
