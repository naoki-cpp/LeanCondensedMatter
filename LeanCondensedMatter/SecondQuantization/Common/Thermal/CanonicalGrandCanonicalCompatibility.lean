import LeanCondensedMatter.Analysis.Operator.Diagonal
import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.CoordinateProjection
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
  have hρ : ρ.op = b.diagonalOp a := by
    apply continuousLinearMap_ext_completedBasis
    intro c
    change ρ.op (b c) = b.diagonalOp a (b c)
    rw [HilbertBasis.diagonalOp_apply_basis b a ha c]
    simpa only [ρ, b, a, completedHilbertBasis_apply] using
      (grandCanonicalGibbsDensityOperator_apply_basis ε β μ hsum c)
  have hfull : HasSum (fun c : Config => b.diagonalTerm a c) ρ.op := by
    rw [hρ]
    exact HilbertBasis.hasSum_diagonalTerm b a ha
  have hblock (N : ℕ) :
      (∑' n : ParticleNumberSector Mode Config N, b.diagonalTerm a n.val) =
        (completedCoordinateProjection
          (fun c : Config => particleNumber (Mode := Mode) c = N)).comp
          (ρ.op.comp (completedCoordinateProjection
            (fun c : Config => particleNumber (Mode := Mode) c = N))) := by
    let P := completedCoordinateProjection
      (fun c : Config => particleNumber (Mode := Mode) c = N)
    let L : (CompletedFock Config →L[ℂ] CompletedFock Config) →L[ℂ]
        (CompletedFock Config →L[ℂ] CompletedFock Config) :=
      (ContinuousLinearMap.mulLeftRight ℂ
        (CompletedFock Config →L[ℂ] CompletedFock Config)) P P
    have hterm (c : Config) :
        L (b.diagonalTerm a c) =
          if particleNumber (Mode := Mode) c = N then b.diagonalTerm a c else 0 := by
      apply ContinuousLinearMap.ext
      intro ψ
      change P ((b.diagonalTerm a c) (P ψ)) =
        (if particleNumber (Mode := Mode) c = N then b.diagonalTerm a c else 0) ψ
      simp only [HilbertBasis.diagonalTerm, smul_apply,
        InnerProductSpace.rankOne_apply, map_smul, b, completedHilbertBasis_apply]
      by_cases hc : particleNumber (Mode := Mode) c = N
      · simp [P, hc, inner_completedBasisState_left,
          completedCoordinateProjection_apply, completedCoordinateProjection_basisState]
      · simp [P, hc, inner_completedBasisState_left,
          completedCoordinateProjection_apply, completedCoordinateProjection_basisState]
    have hfamily :
        (fun c : Config => L (b.diagonalTerm a c)) =
          Function.extend (Subtype.val : ParticleNumberSector Mode Config N → Config)
            (fun n : ParticleNumberSector Mode Config N => b.diagonalTerm a n.val) 0 := by
      funext c
      by_cases hc : particleNumber (Mode := Mode) c = N
      · let n : ParticleNumberSector Mode Config N := ⟨c, hc⟩
        change L (b.diagonalTerm a n.val) =
          Function.extend (Subtype.val : ParticleNumberSector Mode Config N → Config)
            (fun n : ParticleNumberSector Mode Config N => b.diagonalTerm a n.val) 0 n.val
        rw [hterm, ite_eq_left hc, Subtype.val_injective.extend_apply]
      · have hnot : ¬ ∃ n : ParticleNumberSector Mode Config N, n.val = c := by
          rintro ⟨n, hn⟩
          apply hc
          rw [← hn]
          exact n.property
        rw [hterm, ite_eq_right hc, Function.extend_apply' _ _ _ hnot]
        simp
    have hcompressed := hfull.mapL L
    rw [hfamily] at hcompressed
    have hsector := (hasSum_extend_zero Subtype.val_injective).mp hcompressed
    have hL : L ρ.op = P.comp (ρ.op.comp P) := by
      apply ContinuousLinearMap.ext
      intro ψ
      change P (ρ.op (P ψ)) = P (ρ.op (P ψ))
      rfl
    exact hsector.tsum_eq.trans hL
  have hgroups :
      ρ.op = ∑' N : ℕ, ∑' n : ParticleNumberSector Mode Config N,
        b.diagonalTerm a n.val :=
    (hfull.tsum_fiberwise
      (particleNumber (Mode := Mode) (Config := Config))).tsum_eq.symm
  calc
    ρ.op = ∑' N : ℕ, ∑' n : ParticleNumberSector Mode Config N,
        b.diagonalTerm a n.val := hgroups
    _ = _ := by
      apply tsum_congr
      intro N
      by_cases hN : Nonempty (ParticleNumberSector Mode Config N)
      · letI : Nonempty (ParticleNumberSector Mode Config N) := hN
        simp only [dite_eq_left hN]
        rw [hblock N]
        exact grandCanonicalGibbsDensityOperator_compress_sector ε β μ N hsum
      · letI : IsEmpty (ParticleNumberSector Mode Config N) :=
          ⟨fun n => hN ⟨n⟩⟩
        simp only [dite_eq_right hN]
        simp

open Classical in
/-- For the absolutely summable diagonal grand-canonical decomposition, the trace
of the operator-valued sector series can be exchanged with the sector sum.
This is a trace-specific result: operator-norm convergence alone does not
justify interchange of traces for an arbitrary operator series. -/
private theorem grandCanonicalGibbsDensityOperator_trace_tsum_canonical_blocks
    (ε : Mode → ℝ) (β μ : ℝ)
    (hsum : EigenbasisGibbsSummable
      (grandCanonicalEnergy (Config := Config) ε μ) β)
    (A : CompletedFock Config →L[ℂ] CompletedFock Config)
    (hseries : IsTraceClass
      (∑' N : ℕ,
        if hN : Nonempty (ParticleNumberSector Mode Config N) then
          letI : Nonempty (ParticleNumberSector Mode Config N) := hN
          (grandCanonicalSectorProbability (Config := Config) ε β μ N : ℂ) •
            (canonicalFullGibbsDensityOperator (Config := Config) ε β N
              (canonicalGibbsSummable_of_grandCanonical ε β μ N hsum)).op
        else 0)) :
    (hseries.comp_right A).trace =
      ∑' N : ℕ,
        if hN : Nonempty (ParticleNumberSector Mode Config N) then
          letI : Nonempty (ParticleNumberSector Mode Config N) := hN
          (grandCanonicalSectorProbability (Config := Config) ε β μ N : ℂ) *
            (canonicalFullGibbsDensityOperator (Config := Config) ε β N
              (canonicalGibbsSummable_of_grandCanonical ε β μ N hsum)).expectation A
        else 0 := by
  classical
  let ρ := grandCanonicalGibbsDensityOperator (Config := Config) ε β μ hsum
  have hOp := grandCanonicalGibbsDensityOperator_op_eq_tsum_canonical
    (Config := Config) ε β μ hsum
  have htrace : (hseries.comp_right A).trace = ρ.expectation A := by
    rw [ρ.expectation_apply]
    apply IsTraceClass.trace_congr
    simpa only [mul_apply_eq_comp] using
      congrArg (fun T : CompletedFock Config →L[ℂ] CompletedFock Config => T * A)
        hOp.symm
  rw [htrace]
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
  have hfull : HasSum f (ρ.expectation A) := by
    simpa only [f, completedHilbertBasis_apply] using
      (ρ.hasSum_expectation_diagonal A
        (completedHilbertBasis (Config := Config))
        (eigenbasisGibbsProbability (grandCanonicalEnergy ε μ) β) hdiag)
  calc
    ρ.expectation A = ∑' N : ℕ, ∑' n : ParticleNumberSector Mode Config N,
        f n.val :=
      (hfull.tsum_fiberwise
        (particleNumber (Mode := Mode) (Config := Config))).tsum_eq.symm
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

open Classical in
/-- Every bounded grand-canonical expectation is a probability-weighted mixture
of full-Fock canonical expectations. The proof applies the trace-exchange
formula to the operator-valued canonical sector decomposition, and includes
empty sectors without particle-number conservation assumptions on A. -/
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
  have hOp := grandCanonicalGibbsDensityOperator_op_eq_tsum_canonical
    (Config := Config) ε β μ hsum
  have hseries : IsTraceClass
      (∑' N : ℕ,
        if hN : Nonempty (ParticleNumberSector Mode Config N) then
          letI : Nonempty (ParticleNumberSector Mode Config N) := hN
          (grandCanonicalSectorProbability (Config := Config) ε β μ N : ℂ) •
            (canonicalFullGibbsDensityOperator (Config := Config) ε β N
              (canonicalGibbsSummable_of_grandCanonical ε β μ N hsum)).op
        else 0) := by
    rw [← hOp]
    exact ρ.isTraceClass
  have hexchange :=
    grandCanonicalGibbsDensityOperator_trace_tsum_canonical_blocks
      (Config := Config) ε β μ hsum A hseries
  calc
    ρ.expectation A = (ρ.isTraceClass.comp_right A).trace :=
      ρ.expectation_apply A
    _ = (hseries.comp_right A).trace := by
      apply IsTraceClass.trace_congr
      simpa only [mul_apply_eq_comp] using
        congrArg (fun T : CompletedFock Config →L[ℂ] CompletedFock Config => T * A) hOp
    _ = _ := hexchange

end

end Common
end SecondQuantization
