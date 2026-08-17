import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinLimit
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Lorentzian spectral weight for the massive-Dirac Bastin kernel

The pointwise zero-broadening result in `MassiveDiracBastinLimit` deliberately excludes the band
energies.  The missing spectral weight is carried by the retarded-minus-advanced resolvent
difference.  This file exposes that difference as the standard Lorentzian kernel

```text
η / (x² + η²)
```

with `x = E - E_n`, evaluates its finite interval integral, and proves that the mass in every fixed
symmetric neighborhood of the spectral point tends to `π` as `η → 0⁺`.

This is the first integrated zero-broadening step.  It does not yet pair the kernel with an
arbitrary occupation function and therefore does not claim a full delta-distribution theorem.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter QuantumTheory.Transport

/-- Real Lorentzian kernel carrying the scalar retarded-minus-advanced spectral weight. -/
def lorentzianSpectralKernel (offset broadening : ℝ) : ℝ :=
  broadening / (broadening ^ 2 + offset ^ 2)

private theorem complex_offset_add_I_ne_zero
    (offset broadening : ℝ) (hbroadening : broadening ≠ 0) :
    (offset : ℂ) + (broadening : ℂ) * Complex.I ≠ 0 := by
  intro hzero
  have him : broadening = 0 := by
    simpa using congrArg Complex.im hzero
  exact hbroadening him

private theorem complex_offset_sub_I_ne_zero
    (offset broadening : ℝ) (hbroadening : broadening ≠ 0) :
    (offset : ℂ) - (broadening : ℂ) * Complex.I ≠ 0 := by
  intro hzero
  have him : broadening = 0 := by
    simpa using congrArg Complex.im hzero
  exact hbroadening him

/-- Elementary retarded-minus-advanced scalar resolvent identity. -/
theorem inv_add_I_sub_inv_sub_I_eq_lorentzian
    (offset broadening : ℝ) (hbroadening : broadening ≠ 0) :
    ((offset : ℂ) + (broadening : ℂ) * Complex.I)⁻¹ -
        ((offset : ℂ) - (broadening : ℂ) * Complex.I)⁻¹ =
      (-2 * Complex.I) * (lorentzianSpectralKernel offset broadening : ℂ) := by
  have hplus := complex_offset_add_I_ne_zero offset broadening hbroadening
  have hminus := complex_offset_sub_I_ne_zero offset broadening hbroadening
  have hsumReal : broadening ^ 2 + offset ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero hbroadening]
  have hsum : (((broadening ^ 2 + offset ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hsumReal
  have hsumOffset : (((offset ^ 2 + broadening ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    simpa [add_comm] using hsum
  unfold lorentzianSpectralKernel
  push_cast
  field_simp [hplus, hminus, hsum]
  ring_nf
  field_simp [hsumOffset]
  ring

/-- The scalar spectral difference in the two-band Bastin decomposition is exactly a Lorentzian
centered at the selected band energy. -/
theorem spectralDifferenceCoefficient_eq_lorentzian
    (band : Band) (v m px py probeEnergy broadening : ℝ)
    (hbroadening : broadening ≠ 0) :
    spectralDifferenceCoefficient band v m px py probeEnergy broadening =
      (-2 * Complex.I) *
        (lorentzianSpectralKernel
          (probeEnergy - bandEnergy band v m px py) broadening : ℂ) := by
  unfold spectralDifferenceCoefficient projectorResolventCoefficient
    retardedSpectralParameter advancedSpectralParameter
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    inv_add_I_sub_inv_sub_I_eq_lorentzian
      (probeEnergy - bandEnergy band v m px py) broadening hbroadening

/-- Exact finite-interval mass of the Lorentzian kernel. -/
theorem integral_lorentzianSpectralKernel
    (lower upper broadening : ℝ) :
    (∫ offset in lower..upper, lorentzianSpectralKernel offset broadening) =
      Real.arctan (upper / broadening) - Real.arctan (lower / broadening) := by
  simpa [lorentzianSpectralKernel, add_comm] using
    (integral_div_sq_add_sq (a := lower) (b := upper) (c := broadening))

/-- On a symmetric interval the Lorentzian mass is `2 arctan(radius / η)`. -/
theorem integral_lorentzianSpectralKernel_symmetric
    (radius broadening : ℝ) :
    (∫ offset in -radius..radius, lorentzianSpectralKernel offset broadening) =
      2 * Real.arctan (radius / broadening) := by
  rw [integral_lorentzianSpectralKernel]
  rw [show (-radius) / broadening = -(radius / broadening) by ring]
  rw [Real.arctan_neg]
  ring

/-- Every fixed positive symmetric neighborhood captures asymptotic Lorentzian mass `π` as the
broadening tends to zero from the positive side. -/
theorem tendsto_integral_lorentzianSpectralKernel_symmetric
    (radius : ℝ) (hradius : 0 < radius) :
    Tendsto
      (fun broadening : ℝ =>
        ∫ offset in -radius..radius, lorentzianSpectralKernel offset broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds Real.pi) := by
  have hinv : Tendsto (fun broadening : ℝ => broadening⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) atTop :=
    tendsto_inv_nhdsGT_zero
  have hscaled : Tendsto (fun broadening : ℝ => radius * broadening⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
    exact (tendsto_const_nhds : Tendsto (fun _ : ℝ => radius)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds radius)).pos_mul_atTop hradius hinv
  have harctanWithin := Real.tendsto_arctan_atTop.comp hscaled
  have harctan : Tendsto
      (fun broadening : ℝ => Real.arctan (radius / broadening))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.pi / 2)) := by
    have h := tendsto_nhds_of_tendsto_nhdsWithin harctanWithin
    change Tendsto
      (fun broadening : ℝ => Real.arctan (radius * broadening⁻¹))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.pi / 2)) at h
    simpa only [div_eq_mul_inv] using h
  have hmass := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (2 : ℝ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 2)).mul harctan
  have hfun :
      (fun broadening : ℝ =>
        ∫ offset in -radius..radius, lorentzianSpectralKernel offset broadening) =
      (fun broadening : ℝ => 2 * Real.arctan (radius / broadening)) := by
    funext broadening
    exact integral_lorentzianSpectralKernel_symmetric radius broadening
  have hpi : (2 : ℝ) * (Real.pi / 2) = Real.pi := by
    ring
  rw [hfun]
  rw [hpi] at hmass
  exact hmass

end

end AnomalousHall.MassiveDirac
