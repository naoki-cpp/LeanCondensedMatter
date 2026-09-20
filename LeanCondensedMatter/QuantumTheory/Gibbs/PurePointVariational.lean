import LeanCondensedMatter.QuantumTheory.Gibbs.PurePointEntropy
import LeanCondensedMatter.QuantumTheory.Gibbs.FreeEnergy

/-!
# Variational principle for countable pure-point Gibbs data

This file proves the diagonal/classical variational principle directly from countable probability
weights. A competing distribution carries its own normalization, entropy summability, and energy
integrability hypotheses; no bounded observable is introduced for potentially unbounded energy data.
-/

noncomputable section

namespace QuantumTheory

variable {ι : Type*}

/-- A normalized countable probability family with finite Shannon entropy and absolutely integrable
energy against the supplied pure-point spectrum. -/
structure PurePointGibbsCompetitor (E : ι → ℝ) where
  /-- Probability assigned to each pure-point energy level. -/
  probability : ι → ℝ
  /-- Each probability is nonnegative. -/
  nonneg : ∀ i, 0 ≤ probability i
  /-- The probabilities are normalized to total mass one. -/
  hasSum_one : HasSum probability 1
  /-- The Shannon entropy series is summable. -/
  entropySummable : Summable fun i => Real.negMulLog (probability i)
  /-- The mean-energy series is absolutely summable. -/
  energyIntegrable : Summable fun i => ‖probability i * E i‖

namespace PurePointGibbsCompetitor

/-- Shannon entropy of a countable pure-point competitor. -/
noncomputable def entropy (p : PurePointGibbsCompetitor E) : ℝ :=
  ∑' i, Real.negMulLog (p.probability i)

/-- Mean energy of a countable pure-point competitor. -/
noncomputable def energy (p : PurePointGibbsCompetitor E) : ℝ :=
  ∑' i, p.probability i * E i

/-- Helmholtz free energy of a countable pure-point competitor. -/
noncomputable def helmholtzFreeEnergy (p : PurePointGibbsCompetitor E) (β : ℝ) : ℝ :=
  p.energy - (1 / β) * p.entropy

end PurePointGibbsCompetitor

/-- Every normalized countable competitor with finite entropy and absolutely integrable energy has
Helmholtz free energy at least the pure-point Gibbs value. -/
theorem purePointGibbs_helmholtzFreeEnergy_le
    [Nonempty ι] (E : ι → ℝ) (β : ℝ) (hβ : 0 < β)
    (hsum : PurePointGibbsSummable E β) (p : PurePointGibbsCompetitor E) :
    -(1 / β) * Real.log (purePointPartitionFunction E β) ≤
      p.helmholtzFreeEnergy β := by
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
  have hβinv : 0 < 1 / β := by positivity
  have hmul := mul_le_mul_of_nonneg_left hmain hβinv.le
  have hcancel : (1 / β) * (β * p.energy) = p.energy := by
    field_simp
  rw [mul_add, hcancel] at hmul
  change -(1 / β) * Real.log Z ≤
    p.energy - (1 / β) * p.entropy
  linarith

end QuantumTheory
