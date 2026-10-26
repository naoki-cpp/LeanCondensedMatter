import LeanCondensedMatter.Analysis.Operator.TraceClass.Cyclicity
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

noncomputable section

variable {Mode Config : Type*} [OccupationBasis Mode Config]

/-- A particle-number compression of the grand-canonical density equals the
full-Fock zero extension of the canonical density scaled by the probability
of that sector. These are equalities of bounded operators, not of normalized
density operators. No number-conservation condition on an observable is needed. -/
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

/-- The expectation of any bounded full-Fock observable in a summable grand-canonical
Gibbs state is an absolutely convergent sum over sharp-number sectors.
The sector summands are unnormalized, so this includes empty sectors without a
nonemptiness or canonical Gibbs-state hypothesis. -/
theorem grandCanonicalGibbsDensityOperator_expectation_eq_tsum_sector
    (ε : Mode → ℝ) (β μ : ℝ)
    (hsum : EigenbasisGibbsSummable
      (grandCanonicalEnergy (Config := Config) ε μ) β)
    (A : CompletedFock Config →L[ℂ] CompletedFock Config) :
    (grandCanonicalGibbsDensityOperator (Config := Config) ε β μ hsum).expectation A =
      ∑' N : ℕ, ∑' n : ParticleNumberSector Mode Config N,
        (eigenbasisGibbsProbability (grandCanonicalEnergy ε μ) β n.val : ℂ) *
          inner ℂ (completedBasisState n.val) (A (completedBasisState n.val)) := by
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
  have hfull : HasSum f (ρ.expectation A) := by
    simpa only [f, completedHilbertBasis_apply] using
      (ρ.hasSum_expectation_diagonal A
        (completedHilbertBasis (Config := Config))
        (eigenbasisGibbsProbability (grandCanonicalEnergy ε μ) β) hdiag)
  change ρ.expectation A =
    ∑' N : ℕ, ∑' n : ParticleNumberSector Mode Config N, f n.val
  exact (hfull.tsum_fiberwise
    (particleNumber (Mode := Mode) (Config := Config))).tsum_eq.symm

/-- On a nonempty sharp-number sector, the unnormalized contribution to any
bounded grand-canonical expectation equals its probability times the
expectation in the fixed-number canonical state, zero-extended to full Fock. -/
theorem grandCanonicalGibbsDensityOperator_sector_expectation_eq_canonical
    (ε : Mode → ℝ) (β μ : ℝ) (N : ℕ)
    [Nonempty (ParticleNumberSector Mode Config N)]
    (hsum : EigenbasisGibbsSummable
      (grandCanonicalEnergy (Config := Config) ε μ) β)
    (A : CompletedFock Config →L[ℂ] CompletedFock Config) :
    (∑' n : ParticleNumberSector Mode Config N,
      (eigenbasisGibbsProbability (grandCanonicalEnergy ε μ) β n.val : ℂ) *
        inner ℂ (completedBasisState n.val) (A (completedBasisState n.val))) =
      (grandCanonicalSectorProbability (Config := Config) ε β μ N : ℂ) *
        (canonicalFullGibbsDensityOperator (Config := Config) ε β N
          (canonicalGibbsSummable_of_grandCanonical ε β μ N hsum)).expectation A := by
  classical
  let ρ := grandCanonicalGibbsDensityOperator (Config := Config) ε β μ hsum
  let σ := canonicalFullGibbsDensityOperator (Config := Config) ε β N
    (canonicalGibbsSummable_of_grandCanonical ε β μ N hsum)
  let p : ℂ := grandCanonicalSectorProbability (Config := Config) ε β μ N
  let P := completedCoordinateProjection
    (fun c : Config => particleNumber (Mode := Mode) c = N)
  let B := P.comp (A.comp P)
  let w : Config → ℝ :=
    eigenbasisGibbsProbability (grandCanonicalEnergy ε μ) β
  let f : ParticleNumberSector Mode Config N → ℂ := fun n =>
    (w n.val : ℂ) *
      inner ℂ (completedBasisState n.val) (A (completedBasisState n.val))
  let g : Config → ℂ := fun c =>
    (w c : ℂ) * inner ℂ (completedBasisState c) (B (completedBasisState c))
  have hdiag : ∀ c : Config,
      ρ.op ((completedHilbertBasis (Config := Config)) c) =
        (w c : ℂ) • (completedHilbertBasis (Config := Config)) c := by
    intro c
    simpa only [ρ, w, completedHilbertBasis_apply] using
      (grandCanonicalGibbsDensityOperator_apply_basis ε β μ hsum c)
  have hfull : HasSum g (ρ.expectation B) := by
    simpa only [g, completedHilbertBasis_apply] using
      (ρ.hasSum_expectation_diagonal B
        (completedHilbertBasis (Config := Config)) w hdiag)
  have hB (c : Config) :
      inner ℂ (completedBasisState c) (B (completedBasisState c)) =
        if particleNumber (Mode := Mode) c = N then
          inner ℂ (completedBasisState c) (A (completedBasisState c))
        else 0 := by
    by_cases hc : particleNumber (Mode := Mode) c = N
    · simp only [hc, ↓reduceIte]
      change inner ℂ (completedBasisState c)
        (P (A (P (completedBasisState c)))) = _
      rw [show P (completedBasisState c) = completedBasisState c from
        by simp only [P, completedCoordinateProjection_basisState, hc, ↓reduceIte]]
      simp only [P, inner_completedBasisState_left,
        completedCoordinateProjection_apply, hc, ↓reduceIte]
    · simp only [hc, ↓reduceIte]
      change inner ℂ (completedBasisState c)
        (P (A (P (completedBasisState c)))) = 0
      rw [show P (completedBasisState c) = 0 from
        by simp only [P, completedCoordinateProjection_basisState, hc, ↓reduceIte]]
      simp
  have hpoint :
      Function.extend
        (Subtype.val : ParticleNumberSector Mode Config N → Config) f 0 = g := by
    funext c
    by_cases hc : particleNumber (Mode := Mode) c = N
    · let n : ParticleNumberSector Mode Config N := ⟨c, hc⟩
      change Function.extend
        (Subtype.val : ParticleNumberSector Mode Config N → Config)
        f 0 n.val = g n.val
      rw [Subtype.val_injective.extend_apply]
      change (w n.val : ℂ) *
          inner ℂ (completedBasisState n.val) (A (completedBasisState n.val)) =
        (w n.val : ℂ) *
          inner ℂ (completedBasisState n.val) (B (completedBasisState n.val))
      rw [hB n.val]
      simp only [n.property, ↓reduceIte]
    · have hnot : ¬ ∃ n : ParticleNumberSector Mode Config N, n.val = c := by
        rintro ⟨n, hn⟩
        apply hc
        rw [← hn]
        exact n.property
      change Function.extend
        (Subtype.val : ParticleNumberSector Mode Config N → Config) f 0 c = g c
      rw [Function.extend_apply' _ _ _ hnot]
      change (0 : ℂ) = (w c : ℂ) *
        inner ℂ (completedBasisState c) (B (completedBasisState c))
      rw [hB c]
      simp only [hc, ↓reduceIte, mul_zero]
  have hsector : HasSum f (ρ.expectation B) :=
    (hasSum_extend_zero Subtype.val_injective).1 (by
      simpa only [hpoint] using hfull)
  have hcompress : P * (ρ.op * P) = p • σ.op := by
    simpa only [ContinuousLinearMap.mul_def] using
      (grandCanonicalGibbsDensityOperator_compress_sector ε β μ N hsum)
  have hcyclic :
      (ρ.isTraceClass.comp_right B).trace =
        (((ρ.isTraceClass.comp_left P).comp_right P).comp_right A).trace := by
    calc
      _ = ((ρ.isTraceClass.comp_right (P.comp A)).comp_right P).trace := by
        apply ContinuousLinearMap.IsTraceClass.trace_congr
        ext ψ
        simp only [B, ContinuousLinearMap.comp_apply, mul_apply_eq_comp]
      _ = ((ρ.isTraceClass.comp_right (P.comp A)).comp_left P).trace :=
        (ρ.isTraceClass.comp_right (P.comp A)).trace_comp_comm P
      _ = (((ρ.isTraceClass.comp_left P).comp_right P).comp_right A).trace := by
        apply ContinuousLinearMap.IsTraceClass.trace_congr
        ext ψ
        simp only [ContinuousLinearMap.comp_apply, mul_apply_eq_comp]
  have hscaled :
      (((ρ.isTraceClass.comp_left P).comp_right P).comp_right A).trace =
        p * σ.expectation A := by
    calc
      _ = ((σ.isTraceClass.comp_right A).smul p).trace := by
        apply ContinuousLinearMap.IsTraceClass.trace_congr
        change ((P * ρ.op) * P) * A = p • (σ.op * A)
        rw [mul_assoc P ρ.op P, hcompress, smul_mul_assoc]
      _ = p * σ.expectation A := by
        rw [(σ.isTraceClass.comp_right A).trace_smul]
        rfl
  change (∑' n : ParticleNumberSector Mode Config N, f n) = p * σ.expectation A
  calc
    (∑' n : ParticleNumberSector Mode Config N, f n) = ρ.expectation B :=
      hsector.tsum_eq
    _ = (ρ.isTraceClass.comp_right B).trace := ρ.expectation_apply B
    _ = (((ρ.isTraceClass.comp_left P).comp_right P).comp_right A).trace := hcyclic
    _ = p * σ.expectation A := hscaled

open Classical in
/-- Every bounded grand-canonical expectation is a probability-weighted mixture
of full-Fock canonical expectations. Empty particle-number sectors contribute zero;
no particle-number conservation assumption is imposed on the observable. -/
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
  rw [grandCanonicalGibbsDensityOperator_expectation_eq_tsum_sector ε β μ hsum A]
  apply tsum_congr
  intro N
  by_cases hN : Nonempty (ParticleNumberSector Mode Config N)
  · letI : Nonempty (ParticleNumberSector Mode Config N) := hN
    simpa only [dite_eq_left hN] using
      (grandCanonicalGibbsDensityOperator_sector_expectation_eq_canonical
        ε β μ N hsum A)
  · letI : IsEmpty (ParticleNumberSector Mode Config N) :=
      ⟨fun n => hN ⟨n⟩⟩
    simp only [dite_eq_right hN]
    simp

end

end Common
end SecondQuantization
