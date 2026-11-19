import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.CoordinateProjection
import LeanCondensedMatter.Analysis.Operator.TraceClass.DiagonalProjection
import LeanCondensedMatter.SecondQuantization.Common.Thermal.CanonicalCompatibility
import LeanCondensedMatter.SecondQuantization.Common.Thermal.GrandCanonicalSectorDecomposition

set_option linter.style.header false

/-!
# Density-operator compatibility of canonical and grand-canonical Gibbs states

The scalar sector weights, summability, probabilities, and partition-function
decomposition are owned by GrandCanonicalSectorDecomposition. This module
uses those scalar identities to identify the sharp-number compression of the
full-Fock grand-canonical Gibbs density with the zero-extended canonical density
scaled by the sector probability.

The equality holds on the completed occupation Fock space without a finite-mode
assumption or CCR/CAR. The compressed operator need not have trace one.
-/

namespace SecondQuantization
namespace Common

open QuantumTheory
open ContinuousLinearMap

noncomputable section

variable {Mode Config : Type*} [OccupationBasis Mode Config]

/-- A particle-number compression of the grand-canonical density equals the
full-Fock zero extension of the canonical density scaled by the probability
of that sector. This is an equality of bounded operators; the compressed
operator is generally unnormalized and is not itself a density state. -/
theorem grandCanonicalGibbsDensityOperator_compress_sector
    (ε : Mode → ℝ) (β μ : ℝ) (N : ℕ)
    [Nonempty (ParticleNumberSector Mode Config N)]
    (hsum : EigenbasisGibbsSummable
      (grandCanonicalEnergy (Config := Config) ε μ) β) :
    (completedCoordinateProjection
        (fun c : Config => particleNumber (Mode := Mode) c = N)).comp
      ((grandCanonicalGibbsDensityOperator (Config := Config) ε β μ hsum).op.comp
        (completedCoordinateProjection
          (fun c : Config => particleNumber (Mode := Mode) c = N))) =
      (grandCanonicalSectorProbability (Config := Config) ε β μ N : ℂ) •
        (canonicalFullGibbsDensityOperator (Config := Config) ε β N
          (canonicalGibbsSummable_of_grandCanonical ε β μ N hsum)).op := by
  classical
  apply continuousLinearMap_ext_completedBasis
  intro c
  by_cases hc : particleNumber (Mode := Mode) c = N
  · let n : ParticleNumberSector Mode Config N := ⟨c, hc⟩
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      completedCoordinateProjection_basisState]
    simp only [hc, ↓reduceIte]
    rw [grandCanonicalGibbsDensityOperator_apply_basis, map_smul,
      completedCoordinateProjection_basisState]
    simp only [hc, ↓reduceIte]
    rw [smul_apply]
    change
      (eigenbasisGibbsProbability (grandCanonicalEnergy ε μ) β n.val : ℂ) •
        completedBasisState n.val =
      (grandCanonicalSectorProbability ε β μ N : ℂ) •
        (canonicalFullGibbsDensityOperator (Config := Config) ε β N
          (canonicalGibbsSummable_of_grandCanonical ε β μ N hsum)).op
          (completedBasisState n.val)
    rw [canonicalFullGibbsDensityOperator_apply_basis_of_sector, smul_smul]
    simpa only [Complex.ofReal_mul] using
      congrArg (fun z : ℝ => (z : ℂ) • completedBasisState n.val)
        (grandCanonicalGibbsProbability_of_sector ε β μ N hsum n)
  · simp only [ContinuousLinearMap.comp_apply, completedCoordinateProjection_basisState,
      hc, ↓reduceIte, map_zero, smul_apply,
      canonicalFullGibbsDensityOperator_apply_basis_of_ne ε β N
        (canonicalGibbsSummable_of_grandCanonical ε β μ N hsum) c hc, smul_zero]

open Classical in
/-- The grand-canonical density is the operator-norm convergent sum of its
sharp-number blocks. Every nonempty block is the sector probability times the
zero-extended canonical density, while empty sectors contribute zero.
The total operator is trace class; the asserted convergence is in operator norm. -/
theorem grandCanonicalGibbsDensityOperator_op_eq_tsum_canonical
    (ε : Mode → ℝ) (β μ : ℝ)
    (hsum : EigenbasisGibbsSummable
      (grandCanonicalEnergy (Config := Config) ε μ) β) :
    (grandCanonicalGibbsDensityOperator (Config := Config) ε β μ hsum).op =
      ∑' N : ℕ,
        if hN : Nonempty (ParticleNumberSector Mode Config N) then
          letI : Nonempty (ParticleNumberSector Mode Config N) := hN
          (grandCanonicalSectorProbability (Config := Config) ε β μ N : ℂ) •
            (canonicalFullGibbsDensityOperator (Config := Config) ε β N
              (canonicalGibbsSummable_of_grandCanonical ε β μ N hsum)).op
        else 0 := by
  classical
  let ρ := grandCanonicalGibbsDensityOperator (Config := Config) ε β μ hsum
  let b := completedHilbertBasis (Config := Config)
  let a : Config → ℂ := fun c =>
    (eigenbasisGibbsProbability (grandCanonicalEnergy ε μ) β c : ℂ)
  have ha : Summable (fun c => ‖a c‖) := by
    simpa only [a, eigenbasisGibbsProbability, Real.normalizedWeight,
      eigenbasisPartitionFunction, Complex.norm_real] using
      (Real.summable_norm_normalizedWeight
        (eigenbasisBoltzmannWeight (grandCanonicalEnergy (Config := Config) ε μ) β)
        hsum)
  have hfull : HasSum (fun c : Config => b.diagonalTerm a c) ρ.op :=
    HilbertBasis.hasSum_diagonalTerm b a ha
  calc
    ρ.op = ∑' N : ℕ, ∑' n : ParticleNumberSector Mode Config N,
        b.diagonalTerm a n.val :=
      (hfull.tsum_fiberwise
        (particleNumber (Mode := Mode) (Config := Config))).tsum_eq.symm
    _ = _ := by
      apply tsum_congr
      intro N
      by_cases hN : Nonempty (ParticleNumberSector Mode Config N)
      · letI : Nonempty (ParticleNumberSector Mode Config N) := hN
        simp only [dite_eq_left hN]
        rw [completedCoordinateProjection_tsum_diagonalTerm
          (Config := Config)
          (P := fun c : Config => particleNumber (Mode := Mode) c = N)
          a ρ.op hfull]
        exact grandCanonicalGibbsDensityOperator_compress_sector ε β μ N hsum
      · letI : IsEmpty (ParticleNumberSector Mode Config N) :=
          ⟨fun n => hN ⟨n⟩⟩
        simp only [dite_eq_right hN]
        simp

open Classical in
/-- Every bounded grand-canonical expectation is a probability-weighted mixture
of full-Fock canonical expectations. Trace-class summability of the diagonal
expectation series justifies regrouping by particle number; operator-norm
convergence of the density-sector series alone would not justify this exchange.
No particle-number conservation assumption on the bounded observable is needed. -/
theorem grandCanonicalGibbsDensityOperator_expectation_eq_tsum_canonical
    (ε : Mode → ℝ) (β μ : ℝ)
    (hsum : EigenbasisGibbsSummable
      (grandCanonicalEnergy (Config := Config) ε μ) β)
    (A : CompletedFock Config →L[ℂ] CompletedFock Config) :
    (grandCanonicalGibbsDensityOperator (Config := Config) ε β μ hsum).expectation A =
      ∑' N : ℕ,
        if hN : Nonempty (ParticleNumberSector Mode Config N) then
          letI : Nonempty (ParticleNumberSector Mode Config N) := hN
          (grandCanonicalSectorProbability (Config := Config) ε β μ N : ℂ) *
            (canonicalFullGibbsDensityOperator (Config := Config) ε β N
              (canonicalGibbsSummable_of_grandCanonical ε β μ N hsum)).expectation A
        else 0 := by
  classical
  let ρ := grandCanonicalGibbsDensityOperator (Config := Config) ε β μ hsum
  let f : Config → ℂ := fun c =>
    (eigenbasisGibbsProbability (grandCanonicalEnergy ε μ) β c : ℂ) *
      inner ℂ (completedBasisState c) (A (completedBasisState c))
  have hdiag : ∀ c : Config,
      ρ.op ((completedHilbertBasis (Config := Config)) c) =
        (eigenbasisGibbsProbability (grandCanonicalEnergy ε μ) β c : ℂ) •
          (completedHilbertBasis (Config := Config)) c := by
    intro c
    simpa only [ρ, completedHilbertBasis_apply] using
      (grandCanonicalGibbsDensityOperator_apply_basis ε β μ hsum c)
  calc
    ρ.expectation A = ∑' N : ℕ, ∑' n : ParticleNumberSector Mode Config N,
        f n.val := by
      simpa only [f, completedHilbertBasis_apply] using
        (ρ.expectation_eq_tsum_fiberwise A
          (completedHilbertBasis (Config := Config))
          (eigenbasisGibbsProbability (grandCanonicalEnergy ε μ) β) hdiag
          (particleNumber (Mode := Mode) (Config := Config)))
    _ = _ := by
      apply tsum_congr
      intro N
      by_cases hN : Nonempty (ParticleNumberSector Mode Config N)
      · letI : Nonempty (ParticleNumberSector Mode Config N) := hN
        simp only [dite_eq_left hN]
        let hcan := canonicalGibbsSummable_of_grandCanonical ε β μ N hsum
        rw [canonicalFullGibbsDensityOperator_expectation_eq_tsum_sector ε β N hcan A,
          ← tsum_mul_left]
        apply tsum_congr
        intro n
        simpa only [f, Complex.ofReal_mul, mul_assoc] using
          congrArg
            (fun z : ℝ => (z : ℂ) *
              inner ℂ (completedBasisState n.val) (A (completedBasisState n.val)))
            (grandCanonicalGibbsProbability_of_sector ε β μ N hsum n)
      · letI : IsEmpty (ParticleNumberSector Mode Config N) :=
          ⟨fun n => hN ⟨n⟩⟩
        simp only [dite_eq_right hN]
        simp

/-- The trace-norm error from retaining a finite set of particle-number sectors
equals the total probability of the discarded sectors. This specializes the
Hilbert-basis diagonal cutoff theorem; no finite-dimensional assumption is used. -/
theorem grandCanonicalGibbsDensityOperator_traceNorm_complement_projection
    (ε : Mode → ℝ) (β μ : ℝ)
    (hsum : EigenbasisGibbsSummable
      (grandCanonicalEnergy (Config := Config) ε μ) β)
    (F : Finset ℕ) :
    ∃ hres : IsTraceClass
        ((grandCanonicalGibbsDensityOperator (Config := Config) ε β μ hsum).op -
          (completedCoordinateProjection
            (fun c : Config => particleNumber (Mode := Mode) c ∈ F)).comp
            ((grandCanonicalGibbsDensityOperator (Config := Config) ε β μ hsum).op.comp
              (completedCoordinateProjection
                (fun c : Config => particleNumber (Mode := Mode) c ∈ F)))),
      hres.traceNorm =
        ∑' N : ℕ,
          if N ∈ F then 0 else
            grandCanonicalSectorProbability (Config := Config) ε β μ N := by
  classical
  let ρ := grandCanonicalGibbsDensityOperator (Config := Config) ε β μ hsum
  let b := completedHilbertBasis (Config := Config)
  let Q := completedCoordinateProjection
    (fun c : Config => particleNumber (Mode := Mode) c ∈ F)
  let w : Config → ℝ :=
    eigenbasisGibbsProbability (grandCanonicalEnergy ε μ) β
  let tail : Config → ℝ := fun c =>
    if particleNumber (Mode := Mode) c ∈ F then 0 else w c
  have hw : Summable (fun c => ‖w c‖) := by
    simpa only [w, eigenbasisGibbsProbability, Real.normalizedWeight,
      eigenbasisPartitionFunction] using
      (Real.summable_norm_normalizedWeight
        (eigenbasisBoltzmannWeight (grandCanonicalEnergy (Config := Config) ε μ) β)
        hsum)
  have hw_nonneg : ∀ c, 0 ≤ w c := by
    intro c
    exact eigenbasisGibbsProbability_nonneg
      (grandCanonicalEnergy (Config := Config) ε μ) β c
  have hρdiag : ∀ c, ρ.op (b c) = (w c : ℂ) • b c := by
    intro c
    simpa only [ρ, b, w, completedHilbertBasis_apply] using
      (grandCanonicalGibbsDensityOperator_apply_basis ε β μ hsum c)
  have hQdiag : ∀ c, Q (b c) =
      if particleNumber (Mode := Mode) c ∈ F then b c else 0 := by
    intro c
    by_cases hc : particleNumber (Mode := Mode) c ∈ F
    · simpa [Q, b, completedHilbertBasis_apply, hc] using
        (completedCoordinateProjection_basisState
          (fun x : Config => particleNumber (Mode := Mode) x ∈ F) c)
    · simpa [Q, b, completedHilbertBasis_apply, hc] using
        (completedCoordinateProjection_basisState
          (fun x : Config => particleNumber (Mode := Mode) x ∈ F) c)
  obtain ⟨hres, hresNorm⟩ :=
    b.traceNorm_sub_compress_diagonal w hw hw_nonneg ρ.op Q
      (fun c : Config => particleNumber (Mode := Mode) c ∈ F) hρdiag (by
        intro c
        by_cases hc : particleNumber (Mode := Mode) c ∈ F
        · simpa [hc] using hQdiag c
        · simpa [hc] using hQdiag c)
  have ht : Summable (fun c => ‖tail c‖) := by
    refine Summable.of_norm_bounded hw ?_
    intro c
    by_cases hc : particleNumber (Mode := Mode) c ∈ F
    · simp [tail, hc]
    · simp [tail, hc]
  have htailgroup :
      (∑' c : Config, tail c) =
        ∑' N : ℕ,
          if N ∈ F then 0 else
            grandCanonicalSectorProbability (Config := Config) ε β μ N := by
    have hgroups :=
      ((Summable.of_norm ht).hasSum.tsum_fiberwise
        (particleNumber (Mode := Mode) (Config := Config))).tsum_eq
    rw [← hgroups]
    apply tsum_congr
    intro N
    by_cases hN : N ∈ F
    · simp only [if_pos hN]
      calc
        (∑' n : ParticleNumberSector Mode Config N, tail n.val) =
            ∑' _n : ParticleNumberSector Mode Config N, (0 : ℝ) := by
          apply tsum_congr
          intro n
          simp [tail, n.property, hN]
        _ = 0 := tsum_zero
    · simp only [if_neg hN]
      calc
        (∑' n : ParticleNumberSector Mode Config N, tail n.val) =
            ∑' n : ParticleNumberSector Mode Config N, w n.val := by
          apply tsum_congr
          intro n
          simp [tail, n.property, hN]
        _ = _ := by
          simpa only [w] using
            (grandCanonicalSectorProbability_eq_tsum
              (Config := Config) ε β μ N).symm
  refine ⟨hres, ?_⟩
  calc
    hres.traceNorm = ∑' c : Config, tail c := by
      rw [hresNorm]
      apply tsum_congr
      intro c
      by_cases hc : particleNumber (Mode := Mode) c ∈ F
      · simp [tail, hc]
      · simp [tail, hc]
    _ = _ := htailgroup

end

end Common
end SecondQuantization
