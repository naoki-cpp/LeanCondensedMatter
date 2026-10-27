import LeanCondensedMatter.SecondQuantization.Common.Thermal.CanonicalSector
import LeanCondensedMatter.SecondQuantization.Common.Thermal.GrandCanonical

set_option linter.style.header false

/-!
# Grand-canonical scalar data on sharp-number sectors

Fixed-number restriction of grand-canonical Gibbs weights yields the canonical
weights multiplied by fugacity. The resulting sector probabilities are positive
when the sector is nonempty, and their infinite sum is normalized by reindexing
the occupation basis into its fixed-number fibers. Empty sectors contribute
zero. These scalar statements require no finite-mode, CCR/CAR, or bounded-operator
hypotheses.
-/

namespace SecondQuantization
namespace Common

open QuantumTheory

noncomputable section

variable {Mode Config : Type*} [OccupationBasis Mode Config]

/-- Summability of the full grand-canonical Gibbs weights implies summability
of their restriction to every fixed-number sector. This includes sectors with
infinitely many configurations, and requires no nonemptiness hypothesis. -/
theorem canonicalGibbsSummable_of_grandCanonical
    (ε : Mode → ℝ) (β μ : ℝ) (N : ℕ)
    (hsum : EigenbasisGibbsSummable
      (grandCanonicalEnergy (Config := Config) ε μ) β) :
    EigenbasisGibbsSummable
      (fun n : ParticleNumberSector Mode Config N => occupationEnergy ε n.val) β := by
  have hrestricted : EigenbasisGibbsSummable
      (fun n : ParticleNumberSector Mode Config N =>
        grandCanonicalEnergy ε μ n.val) β :=
    hsum.comp_injective Subtype.val_injective
  have hE :
      (fun n : ParticleNumberSector Mode Config N =>
        grandCanonicalEnergy ε μ n.val) =
      (fun n : ParticleNumberSector Mode Config N =>
        occupationEnergy ε n.val - μ * (N : ℝ)) := by
    funext n
    simp [grandCanonicalEnergy, n.property]
  rw [hE] at hrestricted
  simpa only [sub_add_cancel] using
    (eigenbasisGibbsSummable_add_const
      (fun n : ParticleNumberSector Mode Config N =>
        occupationEnergy ε n.val - μ * (N : ℝ))
      β (μ * (N : ℝ)) hrestricted)

/-- Within a fixed-number sector the chemical-potential correction is a
constant fugacity factor multiplying the canonical Boltzmann weight. -/
theorem grandCanonicalBoltzmannWeight_of_sector
    (ε : Mode → ℝ) (β μ : ℝ) (N : ℕ)
    (n : ParticleNumberSector Mode Config N) :
    eigenbasisBoltzmannWeight (grandCanonicalEnergy ε μ) β n.val =
      Real.exp (β * μ * (N : ℝ)) *
        eigenbasisBoltzmannWeight
          (fun m : ParticleNumberSector Mode Config N => occupationEnergy ε m.val) β n := by
  change Real.exp
      (-β * (occupationEnergy ε n.val -
        μ * (particleNumber (Mode := Mode) n.val : ℝ))) =
    Real.exp (β * μ * (N : ℝ)) * Real.exp (-β * occupationEnergy ε n.val)
  rw [n.property]
  rw [show -β * (occupationEnergy ε n.val - μ * (N : ℝ)) =
      β * μ * (N : ℝ) + -β * occupationEnergy ε n.val by ring,
    Real.exp_add]

/-- Probability assigned by the grand-canonical distribution to the
fixed-particle-number sector. It can be zero when the sector is empty. -/
noncomputable def grandCanonicalSectorProbability
    (ε : Mode → ℝ) (β μ : ℝ) (N : ℕ) : ℝ :=
  Real.exp (β * μ * (N : ℝ)) *
    canonicalPartitionFunction (Config := Config) ε β N /
      grandCanonicalPartitionFunction (Config := Config) ε β μ

/-- Every nonempty fixed-number sector has strictly positive probability under a
summable grand-canonical Gibbs distribution. Empty sectors are handled separately. -/
theorem grandCanonicalSectorProbability_pos
    (ε : Mode → ℝ) (β μ : ℝ) (N : ℕ)
    [Nonempty (ParticleNumberSector Mode Config N)]
    (hsum : EigenbasisGibbsSummable
      (grandCanonicalEnergy (Config := Config) ε μ) β) :
    0 < grandCanonicalSectorProbability (Config := Config) ε β μ N := by
  unfold grandCanonicalSectorProbability
  exact div_pos
    (mul_pos (Real.exp_pos _)
      (canonicalPartitionFunction_pos ε β N
        (canonicalGibbsSummable_of_grandCanonical ε β μ N hsum)))
    (grandCanonicalPartitionFunction_pos ε β μ hsum)

/-- Conditioning the grand-canonical occupation probability on a nonempty
sharp-number sector gives its canonical Gibbs occupation probability. -/
theorem grandCanonicalGibbsProbability_of_sector
    (ε : Mode → ℝ) (β μ : ℝ) (N : ℕ)
    [Nonempty (ParticleNumberSector Mode Config N)]
    (hsum : EigenbasisGibbsSummable
      (grandCanonicalEnergy (Config := Config) ε μ) β)
    (n : ParticleNumberSector Mode Config N) :
    eigenbasisGibbsProbability (grandCanonicalEnergy ε μ) β n.val =
      grandCanonicalSectorProbability (Config := Config) ε β μ N *
        eigenbasisGibbsProbability
          (fun m : ParticleNumberSector Mode Config N => occupationEnergy ε m.val) β n := by
  have hZ : grandCanonicalPartitionFunction (Config := Config) ε β μ ≠ 0 :=
    (grandCanonicalPartitionFunction_pos ε β μ hsum).ne'
  have hZN : canonicalPartitionFunction (Config := Config) ε β N ≠ 0 :=
    (canonicalPartitionFunction_pos ε β N
      (canonicalGibbsSummable_of_grandCanonical ε β μ N hsum)).ne'
  change (grandCanonicalPartitionFunction ε β μ)⁻¹ *
      eigenbasisBoltzmannWeight (grandCanonicalEnergy ε μ) β n.val =
    (Real.exp (β * μ * (N : ℝ)) *
      canonicalPartitionFunction ε β N /
      grandCanonicalPartitionFunction ε β μ) *
      ((canonicalPartitionFunction ε β N)⁻¹ *
        eigenbasisBoltzmannWeight
          (fun m : ParticleNumberSector Mode Config N => occupationEnergy ε m.val) β n)
  rw [grandCanonicalBoltzmannWeight_of_sector]
  field_simp [hZ, hZN]

/-- Restricting the grand-canonical Boltzmann sum to one particle-number sector
factors out the fugacity. This identity also covers empty sectors. -/
private theorem grandCanonicalBoltzmannWeight_tsum_sector
    (ε : Mode → ℝ) (β μ : ℝ) (N : ℕ) :
    (∑' n : ParticleNumberSector Mode Config N,
      eigenbasisBoltzmannWeight (grandCanonicalEnergy ε μ) β n.val) =
      Real.exp (β * μ * (N : ℝ)) *
        canonicalPartitionFunction (Config := Config) ε β N := by
  simp_rw [grandCanonicalBoltzmannWeight_of_sector ε β μ N]
  rw [tsum_mul_left]
  rfl

/-- The grand-canonical partition function is the sum of canonical sector
partition functions weighted by fugacity, including empty sectors. -/
theorem grandCanonicalPartitionFunction_eq_tsum_sector
    (ε : Mode → ℝ) (β μ : ℝ)
    (hsum : EigenbasisGibbsSummable
      (grandCanonicalEnergy (Config := Config) ε μ) β) :
    grandCanonicalPartitionFunction (Config := Config) ε β μ =
      ∑' N : ℕ, Real.exp (β * μ * (N : ℝ)) *
        canonicalPartitionFunction (Config := Config) ε β N := by
  have hfull : Summable
      (eigenbasisBoltzmannWeight (grandCanonicalEnergy (Config := Config) ε μ) β) :=
    eigenbasisBoltzmannWeight_summable _ _ hsum
  calc
    grandCanonicalPartitionFunction (Config := Config) ε β μ =
        ∑' c : Config, eigenbasisBoltzmannWeight
          (grandCanonicalEnergy ε μ) β c := rfl
    _ = ∑' N : ℕ, ∑' n : ParticleNumberSector Mode Config N,
          eigenbasisBoltzmannWeight (grandCanonicalEnergy ε μ) β n.val :=
      (hfull.hasSum.tsum_fiberwise
        (particleNumber (Mode := Mode) (Config := Config))).tsum_eq.symm
    _ = ∑' N : ℕ, Real.exp (β * μ * (N : ℝ)) *
          canonicalPartitionFunction (Config := Config) ε β N := by
      apply tsum_congr
      intro N
      exact grandCanonicalBoltzmannWeight_tsum_sector (Config := Config) ε β μ N

/-- The probability of a sharp-number sector is the sum of grand-canonical
occupation probabilities in that sector, including when it is empty.
This identifies the scalar sector distribution without constructing a
normalized canonical density operator. -/
theorem grandCanonicalSectorProbability_eq_tsum
    (ε : Mode → ℝ) (β μ : ℝ) (N : ℕ) :
    grandCanonicalSectorProbability (Config := Config) ε β μ N =
      ∑' n : ParticleNumberSector Mode Config N,
        eigenbasisGibbsProbability (grandCanonicalEnergy ε μ) β n.val := by
  let Z := grandCanonicalPartitionFunction (Config := Config) ε β μ
  have hweighted := grandCanonicalBoltzmannWeight_tsum_sector (Config := Config) ε β μ N
  calc
    grandCanonicalSectorProbability (Config := Config) ε β μ N =
        Z⁻¹ * (Real.exp (β * μ * (N : ℝ)) *
          canonicalPartitionFunction (Config := Config) ε β N) := by
      simp only [grandCanonicalSectorProbability, Z, div_eq_mul_inv]
      ring
    _ = Z⁻¹ * (∑' n : ParticleNumberSector Mode Config N,
          eigenbasisBoltzmannWeight (grandCanonicalEnergy ε μ) β n.val) := by
      rw [hweighted]
    _ = ∑' n : ParticleNumberSector Mode Config N,
          eigenbasisGibbsProbability (grandCanonicalEnergy ε μ) β n.val := by
      rw [← tsum_mul_left]
      rfl

/-- Absolute integrability of the grand-canonical particle-number spectral series.
Normalizability of the Gibbs state alone does not guarantee a finite first moment. -/
def GrandCanonicalParticleNumberIntegrable
    (ε : Mode → ℝ) (β μ : ℝ) : Prop :=
  Summable fun c : Config =>
    ‖eigenbasisGibbsProbability (grandCanonicalEnergy ε μ) β c *
      (particleNumber (Mode := Mode) c : ℝ)‖

/-- Mean particle number as an occupation-basis spectral sum; valid for bosonic and
fermionic configurations alike when the explicit first-moment condition holds. -/
noncomputable def grandCanonicalParticleNumberExpectation
    (ε : Mode → ℝ) (β μ : ℝ) : ℝ :=
  ∑' c : Config,
    eigenbasisGibbsProbability (grandCanonicalEnergy ε μ) β c *
      (particleNumber (Mode := Mode) c : ℝ)

/-- The particle-number mean is the sum of its spectral terms when integrable. -/
theorem hasSum_grandCanonicalParticleNumberExpectation
    (ε : Mode → ℝ) (β μ : ℝ)
    (hint : GrandCanonicalParticleNumberIntegrable (Config := Config) ε β μ) :
    HasSum
      (fun c : Config =>
        eigenbasisGibbsProbability (grandCanonicalEnergy ε μ) β c *
          (particleNumber (Mode := Mode) c : ℝ))
      (grandCanonicalParticleNumberExpectation (Config := Config) ε β μ) :=
  (Summable.of_norm hint).hasSum

/-- The grand-canonical mean particle number is nonnegative, including when its
spectral `tsum` is interpreted by Lean outside the integrable domain. -/
theorem grandCanonicalParticleNumberExpectation_nonneg
    (ε : Mode → ℝ) (β μ : ℝ) :
    0 ≤ grandCanonicalParticleNumberExpectation (Config := Config) ε β μ := by
  unfold grandCanonicalParticleNumberExpectation
  exact tsum_nonneg fun c =>
    mul_nonneg (eigenbasisGibbsProbability_nonneg (grandCanonicalEnergy ε μ) β c)
      (Nat.cast_nonneg (particleNumber (Mode := Mode) c))

/-- The first moment of a grand-canonical particle-number distribution is
the particle-number-weighted occupation-basis sum. The nonnegative count is
unbounded; absolute integrability is therefore required independently of
the existence of a normalized Gibbs state. This is statistics-independent. -/
theorem grandCanonicalParticleNumber_tsum_eq_sector_moment
    (ε : Mode → ℝ) (β μ : ℝ)
    (hint : GrandCanonicalParticleNumberIntegrable (Config := Config) ε β μ) :
    (∑' c : Config,
      eigenbasisGibbsProbability (grandCanonicalEnergy ε μ) β c *
        (particleNumber (Mode := Mode) c : ℝ)) =
      ∑' N : ℕ, (N : ℝ) *
        grandCanonicalSectorProbability (Config := Config) ε β μ N := by
  let f : Config → ℝ := fun c =>
    eigenbasisGibbsProbability (grandCanonicalEnergy ε μ) β c *
      (particleNumber (Mode := Mode) c : ℝ)
  have hf : Summable f := Summable.of_norm hint
  calc
    (∑' c : Config,
      eigenbasisGibbsProbability (grandCanonicalEnergy ε μ) β c *
        (particleNumber (Mode := Mode) c : ℝ)) = ∑' c : Config, f c := rfl
    _ = ∑' N : ℕ, ∑' n : ParticleNumberSector Mode Config N, f n.val :=
      (hf.hasSum.tsum_fiberwise
        (particleNumber (Mode := Mode) (Config := Config))).tsum_eq.symm
    _ = ∑' N : ℕ, (N : ℝ) *
        grandCanonicalSectorProbability (Config := Config) ε β μ N := by
      apply tsum_congr
      intro N
      calc
        (∑' n : ParticleNumberSector Mode Config N, f n.val) =
            ∑' n : ParticleNumberSector Mode Config N,
              (N : ℝ) *
                eigenbasisGibbsProbability (grandCanonicalEnergy ε μ) β n.val := by
          apply tsum_congr
          intro n
          simp only [f, n.property]
          ring
        _ = (N : ℝ) *
            (∑' n : ParticleNumberSector Mode Config N,
              eigenbasisGibbsProbability (grandCanonicalEnergy ε μ) β n.val) := by
          rw [tsum_mul_left]
        _ = (N : ℝ) *
            grandCanonicalSectorProbability (Config := Config) ε β μ N := by
          rw [← grandCanonicalSectorProbability_eq_tsum ε β μ N]

/-- The grand-canonical sector probabilities form a normalized distribution
over all natural particle numbers, with empty sectors assigned probability zero. -/
theorem grandCanonicalSectorProbability_tsum_eq_one
    (ε : Mode → ℝ) (β μ : ℝ)
    (hsum : EigenbasisGibbsSummable
      (grandCanonicalEnergy (Config := Config) ε μ) β) :
    (∑' N : ℕ, grandCanonicalSectorProbability (Config := Config) ε β μ N) = 1 := by
  change (∑' N : ℕ, (Real.exp (β * μ * (N : ℝ)) *
      canonicalPartitionFunction (Config := Config) ε β N) /
      grandCanonicalPartitionFunction (Config := Config) ε β μ) = 1
  rw [tsum_div_const, ← grandCanonicalPartitionFunction_eq_tsum_sector ε β μ hsum]
  exact div_self (grandCanonicalPartitionFunction_pos ε β μ hsum).ne'

end

end Common
end SecondQuantization
