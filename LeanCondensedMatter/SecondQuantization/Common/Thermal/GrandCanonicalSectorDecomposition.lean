import LeanCondensedMatter.SecondQuantization.Common.Thermal.CanonicalGrandCanonicalCompatibility

set_option linter.style.header false

/-!
# Decomposition of grand-canonical partition functions by particle number

The occupation basis is canonically partitioned into its fixed-number fibers.
Summability of the grand-canonical Boltzmann weights makes the resulting
infinite sector sum genuine, without assuming finite mode or configuration types.
Empty sectors contribute zero. No CCR/CAR assumptions enter the proof.
-/

namespace SecondQuantization
namespace Common

open QuantumTheory

noncomputable section

variable {Mode Config : Type*} [OccupationBasis Mode Config]

/-- The grand-canonical partition function is the sum of canonical sector
partition functions weighted by fugacity, including empty sectors. -/
theorem grandCanonicalPartitionFunction_eq_tsum_sector
    (ε : Mode → ℝ) (β μ : ℝ)
    (hsum : EigenbasisGibbsSummable
      (grandCanonicalEnergy (Config := Config) ε μ) β) :
    grandCanonicalPartitionFunction (Config := Config) ε β μ =
      ∑' N : ℕ, Real.exp (β * μ * (N : ℝ)) *
        canonicalPartitionFunction (Config := Config) ε β N := by
  let e : (Σ N : ℕ, ParticleNumberSector Mode Config N) ≃ Config :=
    Equiv.sigmaFiberEquiv (particleNumber (Mode := Mode) (Config := Config))
  have hfull : Summable
      (eigenbasisBoltzmannWeight (grandCanonicalEnergy (Config := Config) ε μ) β) :=
    eigenbasisBoltzmannWeight_summable _ _ hsum
  have hfiber : Summable
      (fun x : Σ N : ℕ, ParticleNumberSector Mode Config N =>
        eigenbasisBoltzmannWeight (grandCanonicalEnergy ε μ) β (e x)) :=
    hfull.comp_injective e.injective
  calc
    grandCanonicalPartitionFunction (Config := Config) ε β μ =
        ∑' c : Config, eigenbasisBoltzmannWeight
          (grandCanonicalEnergy ε μ) β c := rfl
    _ = ∑' x : Σ N : ℕ, ParticleNumberSector Mode Config N,
          eigenbasisBoltzmannWeight (grandCanonicalEnergy ε μ) β (e x) :=
      (e.tsum_eq _).symm
    _ = ∑' N : ℕ, ∑' n : ParticleNumberSector Mode Config N,
          eigenbasisBoltzmannWeight (grandCanonicalEnergy ε μ) β n.val := by
      rw [hfiber.tsum_sigma]
      simp only [e, Equiv.sigmaFiberEquiv_apply]
    _ = ∑' N : ℕ, Real.exp (β * μ * (N : ℝ)) *
          canonicalPartitionFunction (Config := Config) ε β N := by
      apply tsum_congr
      intro N
      calc
        (∑' n : ParticleNumberSector Mode Config N,
          eigenbasisBoltzmannWeight (grandCanonicalEnergy ε μ) β n.val) =
            ∑' n : ParticleNumberSector Mode Config N,
              Real.exp (β * μ * (N : ℝ)) *
                eigenbasisBoltzmannWeight
                  (fun m : ParticleNumberSector Mode Config N =>
                    occupationEnergy ε m.val) β n := by
          apply tsum_congr
          intro n
          exact grandCanonicalBoltzmannWeight_of_sector ε β μ N n
        _ = Real.exp (β * μ * (N : ℝ)) *
            canonicalPartitionFunction (Config := Config) ε β N := by
          rw [tsum_mul_left]
          rfl

/-- The grand-canonical sector probabilities form a normalized distribution
over all natural particle numbers, with empty sectors assigned probability zero. -/
theorem grandCanonicalSectorProbability_tsum_eq_one
    (ε : Mode → ℝ) (β μ : ℝ)
    (hsum : EigenbasisGibbsSummable
      (grandCanonicalEnergy (Config := Config) ε μ) β) :
    (∑' N : ℕ, grandCanonicalSectorProbability (Config := Config) ε β μ N) = 1 := by
  have hΞ : grandCanonicalPartitionFunction (Config := Config) ε β μ ≠ 0 :=
    (grandCanonicalPartitionFunction_pos ε β μ hsum).ne'
  calc
    (∑' N : ℕ, grandCanonicalSectorProbability (Config := Config) ε β μ N) =
        ∑' N : ℕ, (Real.exp (β * μ * (N : ℝ)) *
          canonicalPartitionFunction (Config := Config) ε β N) /
          grandCanonicalPartitionFunction (Config := Config) ε β μ := rfl
    _ = (∑' N : ℕ, Real.exp (β * μ * (N : ℝ)) *
          canonicalPartitionFunction (Config := Config) ε β N) /
            grandCanonicalPartitionFunction (Config := Config) ε β μ := by
      rw [tsum_div_const]
    _ = 1 := by
      rw [← grandCanonicalPartitionFunction_eq_tsum_sector ε β μ hsum]
      exact div_self hΞ

end

end Common
end SecondQuantization
