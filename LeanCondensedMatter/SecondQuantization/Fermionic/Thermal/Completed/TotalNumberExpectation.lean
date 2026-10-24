import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.Gibbs
import LeanCondensedMatter.SecondQuantization.Common.Thermal.GrandCanonicalSectorDecomposition
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Diagonal

set_option linter.style.header false

/-!
# Completed free-fermion grand-canonical total-number expectation

The completed total-number operator is genuinely unbounded, so it is not passed to
`DensityOperator.expectation`, whose observable argument is bounded. Instead its Gibbs expectation
is the spectral series of its occupation-basis eigenvalues. Absolute convergence is tracked by an
explicit total-number integrability condition; existence of the completed free Gibbs density state
is required only by the bridge back to the density operator.

The operator and its maximal domain remain owned by `Fermionic.CompletedSpace.Diagonal`. This module
owns only the thermal integrability condition and expectation for that concrete observable. Generic
pure-point energy expectations remain in `QuantumTheory.Gibbs.EigenbasisExpectation`; no parallel
public arbitrary-diagonal expectation API is introduced here.
-/

namespace SecondQuantization
namespace Fermionic

open QuantumTheory

noncomputable section

variable {Mode : Type*}

/-- Integrability condition for the completed total particle-number spectral series. State
existence is deliberately not part of this scalar summability predicate. -/
def GrandCanonicalTotalNumberIntegrable
    (ε : Mode → ℝ) (β μ : ℝ) : Prop :=
  Summable fun n : Occupation Mode =>
    ‖eigenbasisGibbsProbability (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β n * (particleNumber n : ℝ)‖

/-- Thermal expectation of the completed total particle-number operator, defined by its real
occupation-basis spectral series. -/
noncomputable def grandCanonicalTotalNumberExpectation
    (ε : Mode → ℝ) (β μ : ℝ) : ℝ :=
  ∑' n : Occupation Mode,
    eigenbasisGibbsProbability (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β n * (particleNumber n : ℝ)

/-- Under the explicit number-integrability hypothesis, the total particle-number expectation is
represented by an absolutely convergent occupation-basis series. -/
theorem hasSum_grandCanonicalTotalNumberExpectation
    (ε : Mode → ℝ) (β μ : ℝ) (hint : GrandCanonicalTotalNumberIntegrable ε β μ) :
    HasSum
      (fun n : Occupation Mode =>
        eigenbasisGibbsProbability (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β n * (particleNumber n : ℝ))
      (grandCanonicalTotalNumberExpectation ε β μ) := by
  exact (Summable.of_norm hint).hasSum

/-- The grand-canonical mean particle number is the first moment of the
sharp-number sector distribution. Unlike bounded-observable sector mixing,
this identity requires integrability of the unbounded number operator. -/
theorem grandCanonicalTotalNumberExpectation_eq_tsum_sector
    (ε : Mode → ℝ) (β μ : ℝ)
    (hint : GrandCanonicalTotalNumberIntegrable ε β μ) :
    grandCanonicalTotalNumberExpectation ε β μ =
      ∑' N : ℕ, (N : ℝ) *
        Common.grandCanonicalSectorProbability (Config := Occupation Mode) ε β μ N := by
  let f : Occupation Mode → ℝ := fun c =>
    eigenbasisGibbsProbability
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β c *
        (particleNumber c : ℝ)
  have hf : Summable f := Summable.of_norm hint
  let e : (Σ N : ℕ, Common.ParticleNumberSector Mode (Occupation Mode) N) ≃
      Occupation Mode :=
    Equiv.sigmaFiberEquiv
      (Common.particleNumber (Mode := Mode) (Config := Occupation Mode))
  have hSigma :
      Summable (fun x : Σ N : ℕ, Common.ParticleNumberSector Mode (Occupation Mode) N =>
        f (e x)) := hf.comp_injective e.injective
  calc
    grandCanonicalTotalNumberExpectation ε β μ = ∑' c : Occupation Mode, f c := rfl
    _ = ∑' x : Σ N : ℕ, Common.ParticleNumberSector Mode (Occupation Mode) N,
          f (e x) := (e.tsum_eq _).symm
    _ = ∑' N : ℕ, ∑' n : Common.ParticleNumberSector Mode (Occupation Mode) N,
          f n.val := by
      rw [hSigma.tsum_sigma]
      simp only [e, Equiv.sigmaFiberEquiv_apply]
    _ = ∑' N : ℕ, (N : ℝ) *
        Common.grandCanonicalSectorProbability (Config := Occupation Mode) ε β μ N := by
      apply tsum_congr
      intro N
      calc
        (∑' n : Common.ParticleNumberSector Mode (Occupation Mode) N, f n.val) =
            ∑' n : Common.ParticleNumberSector Mode (Occupation Mode) N,
              (N : ℝ) *
                eigenbasisGibbsProbability
                  (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β n.val := by
          apply tsum_congr
          intro n
          simp only [f, n.property]
          ring
        _ = (N : ℝ) *
            (∑' n : Common.ParticleNumberSector Mode (Occupation Mode) N,
              eigenbasisGibbsProbability
                (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β n.val) := by
          rw [tsum_mul_left]
        _ = (N : ℝ) *
            Common.grandCanonicalSectorProbability (Config := Occupation Mode) ε β μ N := by
          rw [← Common.grandCanonicalSectorProbability_eq_tsum ε β μ N]

/-- The completed free total-number expectation is nonnegative. -/
theorem grandCanonicalTotalNumberExpectation_nonneg
    (ε : Mode → ℝ) (β μ : ℝ) :
    0 ≤ grandCanonicalTotalNumberExpectation ε β μ := by
  unfold grandCanonicalTotalNumberExpectation
  exact tsum_nonneg fun n =>
    mul_nonneg (eigenbasisGibbsProbability_nonneg (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β n)
      (Nat.cast_nonneg (particleNumber n))

/-- On each occupation basis state, the diagonal matrix element of the composed completed Gibbs
density operator and total-number operator is the corresponding Gibbs probability times particle
number. -/
theorem grandCanonicalGibbsDensityOperator_totalNumber_diagonalTerm
    (ε : Mode → ℝ) (β μ : ℝ) (hsum : EigenbasisGibbsSummable
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β)
    (n : Occupation Mode) :
    inner ℂ (completedBasisState n)
        ((Common.grandCanonicalGibbsDensityOperator (Config := Occupation Mode) ε β μ hsum).op
          (completedTotalNumberOperator
            ⟨completedBasisState n, completedBasisState_mem_completedTotalNumberDomain n⟩)) =
      (eigenbasisGibbsProbability (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β n *
        (particleNumber n : ℝ) : ℝ) := by
  have hnorm : ‖completedBasisState n‖ = 1 := by
    rw [← completedOccupationHilbertBasis_apply]
    exact (completedOccupationHilbertBasis (Mode := Mode)).orthonormal.norm_eq_one n
  rw [completedTotalNumberOperator_basisState, map_smul,
    grandCanonicalGibbsDensityOperator_apply_basis, inner_smul_right, inner_smul_right,
    inner_self_eq_norm_sq_to_K, hnorm]
  norm_num
  ring

/-- The diagonal matrix elements of the actual completed Gibbs density operator composed with the
completed total-number operator sum to the real spectral expectation. -/
theorem hasSum_grandCanonicalGibbsDensityOperator_totalNumber_diagonal
    (ε : Mode → ℝ) (β μ : ℝ) (hsum : EigenbasisGibbsSummable
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β)
    (hint : GrandCanonicalTotalNumberIntegrable ε β μ) :
    HasSum
      (fun n : Occupation Mode =>
        inner ℂ (completedBasisState n)
          ((Common.grandCanonicalGibbsDensityOperator (Config := Occupation Mode) ε β μ hsum).op
            (completedTotalNumberOperator
              ⟨completedBasisState n, completedBasisState_mem_completedTotalNumberDomain n⟩)))
      (grandCanonicalTotalNumberExpectation ε β μ : ℂ) := by
  have hcast :=
    (hasSum_grandCanonicalTotalNumberExpectation ε β μ hint).mapL Complex.ofRealCLM
  simp only [Complex.ofRealCLM_apply] at hcast
  simpa only [grandCanonicalGibbsDensityOperator_totalNumber_diagonalTerm] using hcast

end
end Fermionic
end SecondQuantization
