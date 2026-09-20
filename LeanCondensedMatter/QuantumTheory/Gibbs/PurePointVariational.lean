import LeanCondensedMatter.QuantumTheory.Gibbs.PurePointEntropy
import LeanCondensedMatter.QuantumTheory.Gibbs.FreeEnergy

/-!
# Variational principle for countable pure-point Gibbs data

This file proves the diagonal/classical variational principle directly from countable probability
weights. A competing distribution carries normalization and absolute energy integrability; finite
entropy is derived from the countable Gibbs bound rather than assumed separately. No bounded
observable is introduced for potentially unbounded energy data.
-/

noncomputable section

namespace QuantumTheory

variable {ι : Type*}

/-- A normalized countable probability family with absolutely integrable energy against the
supplied pure-point spectrum. Finite Shannon entropy follows from the Gibbs bound. -/
structure PurePointGibbsCompetitor (E : ι → ℝ) where
  /-- Probability assigned to each pure-point energy level. -/
  probability : ι → ℝ
  /-- Each probability is nonnegative. -/
  nonneg : ∀ i, 0 ≤ probability i
  /-- The probabilities are normalized to total mass one. -/
  hasSum_one : HasSum probability 1
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
  have hqsum_le : ∑' i, q i ≤ Z := by
    rfl
  have hEnergy : Summable fun i => p.probability i * E i :=
    Summable.of_norm p.energyIntegrable
  have hlog : ∀ i, -Real.log (q i) ≤ β * E i := by
    intro i
    have hlogEq : -Real.log (q i) = β * E i := by
      simp [q, purePointBoltzmannWeight]
    exact hlogEq.le
  obtain ⟨-, hmain'⟩ :=
    summable_negMulLog_and_tsum_le_gibbs
      p.probability q E β Z p.nonneg
      p.hasSum_one.summable p.hasSum_one.tsum_eq hEnergy
      hqsum hqsum_le (fun i => purePointBoltzmannWeight_pos E β i) hZpos hlog
  have hmain : p.entropy ≤ β * p.energy + Real.log Z := by
    simpa [PurePointGibbsCompetitor.entropy, PurePointGibbsCompetitor.energy] using hmain'
  have hβinv : 0 < 1 / β := by positivity
  have hmul := mul_le_mul_of_nonneg_left hmain hβinv.le
  have hcancel : (1 / β) * (β * p.energy) = p.energy := by
    field_simp
  rw [mul_add, hcancel] at hmul
  change -(1 / β) * Real.log Z ≤
    p.energy - (1 / β) * p.entropy
  linarith

end QuantumTheory
