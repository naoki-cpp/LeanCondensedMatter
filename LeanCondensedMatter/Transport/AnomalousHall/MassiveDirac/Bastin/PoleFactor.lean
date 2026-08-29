import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Bastin.Interband
import LeanCondensedMatter.Analysis.Lorentzian.Kernel
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Massive-Dirac interband Bastin pole factor

For a target band `n`, the interband Bastin pair has source band `oppositeBand n`.  Its scalar
retarded-minus-advanced factor is the Lorentzian pole centered at `E_n`; the remaining retarded and
advanced opposite-band resolvent squares are regular spectators multiplying the two current-trace
orderings.

This file separates those pieces exactly and proves the regular spectator/current factor converges
at the target-band pole to the inverse-gap-squared antisymmetric current block.  Together with the
Berry numerator bridge, this is the local coefficient that the occupation-weighted Lorentzian
energy integral must extract next.

No energy integration or momentum integration is performed here.
-/

namespace AnomalousHall.MassiveDirac

open QuantumTheory Transport

noncomputable section

/-- The regular spectator/current factor left after extracting the target-band Lorentzian pole. -/
def interbandBastinRegularFactor
    (mass velocity kx ky energy broadening : ℝ) (n : DiracBand) : ℂ :=
  let m := oppositeBand n
  (retardedBandResolvent mass mass velocity kx ky energy broadening) ^ 2 *
      currentTraceYX mass velocity kx ky n m -
    (advancedBandResolvent mass mass velocity kx ky energy broadening) ^ 2 *
      currentTraceYX mass velocity kx ky m n

/-- The opposite-band spectral separation at the target-band energy is the signed band gap. -/
theorem oppositeBandEnergy_sub_targetBandEnergy
    (mass velocity kx ky : ℝ) (n : DiracBand) :
    bandEnergy mass velocity kx ky n -
        bandEnergy mass velocity kx ky (oppositeBand n) =
      (2 * n.sign : ℝ) * diracEnergy mass velocity kx ky := by
  cases n <;> simp [bandEnergy, oppositeBand, DiracBand.sign]

/-- At zero broadening and target-band energy, the regular factor is the inverse-gap-squared
antisymmetric current block. -/
theorem interbandBastinRegularFactor_at_pole
    (mass velocity kx ky : ℝ) (n : DiracBand)
    (hgap : diracEnergy mass velocity kx ky ≠ 0) :
    interbandBastinRegularFactor mass velocity kx ky
        (bandEnergy mass velocity kx ky n) 0 n =
      ((4 * (diracEnergy mass velocity kx ky) ^ 2 : ℝ) : ℂ)⁻¹ *
        (currentTraceYX mass velocity kx ky n (oppositeBand n) -
          currentTraceYX mass velocity kx ky (oppositeBand n) n) := by
  let gap : ℝ := diracEnergy mass velocity kx ky
  have hgap4 : ((4 * gap ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) (sq_ne_zero.mpr hgap)
  have hsep := oppositeBandEnergy_sub_targetBandEnergy mass velocity kx ky n
  unfold interbandBastinRegularFactor
  simp only [retardedBandResolvent, advancedBandResolvent]
  rw [retardedSpectralParameter]
  rw [advancedSpectralParameter]
  push_cast
  simp only [Complex.ofReal_zero, zero_mul, add_zero, sub_zero]
  have hden :
      ((bandEnergy mass velocity kx ky n : ℂ) -
          (bandEnergy mass velocity kx ky (oppositeBand n) : ℂ)) ^ 2 =
        ((4 * gap ^ 2 : ℝ) : ℂ) := by
    rw [← ofReal_sub]
    rw [show bandEnergy mass velocity kx ky n -
        bandEnergy mass velocity kx ky (oppositeBand n) =
          (2 * n.sign : ℝ) * gap by simpa [gap] using hsep]
    push_cast
    cases n <;> simp [DiracBand.sign]
    <;> ring
  rw [show ((bandEnergy mass velocity kx ky n : ℂ) -
      (bandEnergy mass velocity kx ky (oppositeBand n) : ℂ))⁻¹ ^ 2 =
      (((4 * gap ^ 2 : ℝ) : ℂ))⁻¹ by
    rw [← inv_pow, hden]]
  ring

/-- The regular factor is jointly continuous at the isolated target pole whenever the band gap is
nonzero. -/
theorem continuousAt_interbandBastinRegularFactor_pole
    (mass velocity kx ky : ℝ) (n : DiracBand)
    (hgap : diracEnergy mass velocity kx ky ≠ 0) :
    ContinuousAt
      (fun p : ℝ × ℝ =>
        interbandBastinRegularFactor mass velocity kx ky
          (bandEnergy mass velocity kx ky n + p.1) p.2 n)
      (0, 0) := by
  let target : ℝ := bandEnergy mass velocity kx ky n
  let spectator : ℝ := bandEnergy mass velocity kx ky (oppositeBand n)
  have hsep : target - spectator ≠ 0 := by
    have h := oppositeBandEnergy_sub_targetBandEnergy mass velocity kx ky n
    dsimp [target, spectator]
    rw [h]
    exact mul_ne_zero (by cases n <;> norm_num [DiracBand.sign]) hgap
  have hretDen : ContinuousAt
      (fun p : ℝ × ℝ =>
        (retardedSpectralParameter (target + p.1) p.2 - (spectator : ℂ)))
      (0, 0) := by fun_prop
  have hretNe :
      retardedSpectralParameter (target + (0 : ℝ)) 0 - (spectator : ℂ) ≠ 0 := by
    simp [retardedSpectralParameter, hsep]
  have hretInv : ContinuousAt
      (fun p : ℝ × ℝ =>
        (retardedSpectralParameter (target + p.1) p.2 - (spectator : ℂ))⁻¹)
      (0, 0) := hretDen.inv₀ hretNe
  have hadvDen : ContinuousAt
      (fun p : ℝ × ℝ =>
        (advancedSpectralParameter (target + p.1) p.2 - (spectator : ℂ)))
      (0, 0) := by fun_prop
  have hadvNe :
      advancedSpectralParameter (target + (0 : ℝ)) 0 - (spectator : ℂ) ≠ 0 := by
    simp [advancedSpectralParameter, hsep]
  have hadvInv : ContinuousAt
      (fun p : ℝ × ℝ =>
        (advancedSpectralParameter (target + p.1) p.2 - (spectator : ℂ))⁻¹)
      (0, 0) := hadvDen.inv₀ hadvNe
  unfold interbandBastinRegularFactor retardedBandResolvent advancedBandResolvent
  dsimp [target, spectator] at hretInv hadvInv ⊢
  fun_prop

end
end AnomalousHall.MassiveDirac
