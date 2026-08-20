import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinZeroTemperatureRadialDCT
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Sharp occupied radial profile for the zero-temperature Bastin limit

The finite-radial dominated-convergence theorem keeps the exact half-weight at a Fermi-surface
pole.  For comparison with the usual occupied clean shell, it is useful to separate that pointwise
boundary value from the sharp zero-temperature profile that is full below the Fermi level and zero
above it.

This file performs only that measure-zero step.  It proves pointwise agreement away from the Fermi
surface and then identifies the two finite radial integrals whenever the Fermi-surface locus inside
the cutoff interval is contained in one point.  The model-specific proof that the massive-Dirac
radial dispersion has at most one such point is deliberately left to the next slice.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter MeasureTheory Set

/-- Sharp zero-temperature radial clean profile: use the full clean interband-pair density below
`ε_F` and zero above it.  The equality case is assigned zero here; its exact half-weight is retained
in `radialZeroTemperatureInterbandBastinPairLimitDensity` and removed only at the integral level. -/
def sharpRadialZeroTemperatureInterbandBastinPairLimitDensity
    (band : Band) (e v m fermiEnergy p : ℝ) : ℝ :=
  if bandEnergy band v m p 0 < fermiEnergy then
    radialCleanInterbandBastinPairLimitDensity band e v m p
  else
    0

/-- Finite radial integral of the sharp occupied clean profile. -/
def finiteRadialSharpZeroTemperatureInterbandBastinPairLimitIntegral
    (band : Band) (e v m fermiEnergy pMax : ℝ) : ℝ :=
  ∫ p in Set.Icc 0 pMax,
    sharpRadialZeroTemperatureInterbandBastinPairLimitDensity
      band e v m fermiEnergy p

/-- Below the Fermi level the unified zero-temperature radial target is exactly the full clean
interband-pair radial density. -/
theorem radialZeroTemperatureInterbandBastinPairLimitDensity_eq_clean_of_occupied
    (band : Band) (e v m fermiEnergy p : ℝ)
    (hoccupied : bandEnergy band v m p 0 < fermiEnergy) :
    radialZeroTemperatureInterbandBastinPairLimitDensity
        band e v m fermiEnergy p =
      radialCleanInterbandBastinPairLimitDensity band e v m p := by
  unfold radialZeroTemperatureInterbandBastinPairLimitDensity
    radialCleanInterbandBastinPairLimitDensity cleanInterbandBastinPairLimitDensity
  rw [zeroTemperatureLorentzianPoleWeight_of_occupied hoccupied]

/-- Above the Fermi level the unified zero-temperature radial target vanishes. -/
theorem radialZeroTemperatureInterbandBastinPairLimitDensity_eq_zero_of_unoccupied
    (band : Band) (e v m fermiEnergy p : ℝ)
    (hunoccupied : fermiEnergy < bandEnergy band v m p 0) :
    radialZeroTemperatureInterbandBastinPairLimitDensity
        band e v m fermiEnergy p = 0 := by
  unfold radialZeroTemperatureInterbandBastinPairLimitDensity
  rw [zeroTemperatureLorentzianPoleWeight_of_unoccupied hunoccupied] <;> ring_nf

/-- Exactly at the Fermi surface the unified radial target keeps one half of the clean density. -/
theorem radialZeroTemperatureInterbandBastinPairLimitDensity_eq_half_clean_of_fermiSurface
    (band : Band) (e v m fermiEnergy p : ℝ)
    (hfermi : bandEnergy band v m p 0 = fermiEnergy) :
    radialZeroTemperatureInterbandBastinPairLimitDensity
        band e v m fermiEnergy p =
      (1 / 2 : ℝ) * radialCleanInterbandBastinPairLimitDensity band e v m p := by
  unfold radialZeroTemperatureInterbandBastinPairLimitDensity
    radialCleanInterbandBastinPairLimitDensity cleanInterbandBastinPairLimitDensity
  rw [hfermi, zeroTemperatureLorentzianPoleWeight_at_fermi_surface] <;> ring_nf

/-- Away from the Fermi surface, the unified target and the sharp occupied clean profile agree
pointwise. -/
theorem radialZeroTemperatureInterbandBastinPairLimitDensity_eq_sharp_of_ne
    (band : Band) (e v m fermiEnergy p : ℝ)
    (hne : bandEnergy band v m p 0 ≠ fermiEnergy) :
    radialZeroTemperatureInterbandBastinPairLimitDensity
        band e v m fermiEnergy p =
      sharpRadialZeroTemperatureInterbandBastinPairLimitDensity
        band e v m fermiEnergy p := by
  unfold sharpRadialZeroTemperatureInterbandBastinPairLimitDensity
  by_cases hoccupied : bandEnergy band v m p 0 < fermiEnergy
  · rw [if_pos hoccupied]
    exact radialZeroTemperatureInterbandBastinPairLimitDensity_eq_clean_of_occupied
      band e v m fermiEnergy p hoccupied
  · rw [if_neg hoccupied]
    have hunoccupied : fermiEnergy < bandEnergy band v m p 0 := by
      exact lt_of_le_of_ne (le_of_not_gt hoccupied) (Ne.symm hne)
    exact radialZeroTemperatureInterbandBastinPairLimitDensity_eq_zero_of_unoccupied
      band e v m fermiEnergy p hunoccupied

/-- If the Fermi-surface locus in the finite radial interval is contained in one point, the exact
half-weight and the sharp occupied convention have the same radial integral.  This is the explicit
measure-zero bridge needed after the finite-radial dominated-convergence theorem. -/
theorem finiteRadialZeroTemperatureInterbandBastinPairLimitIntegral_eq_sharp_of_fermi_unique
    (band : Band) (e v m fermiEnergy pMax pF : ℝ)
    (hfermiUnique : ∀ p ∈ Set.Icc (0 : ℝ) pMax,
      bandEnergy band v m p 0 = fermiEnergy → p = pF) :
    finiteRadialZeroTemperatureInterbandBastinPairLimitIntegral
        band e v m fermiEnergy pMax =
      finiteRadialSharpZeroTemperatureInterbandBastinPairLimitIntegral
        band e v m fermiEnergy pMax := by
  unfold finiteRadialZeroTemperatureInterbandBastinPairLimitIntegral
    finiteRadialSharpZeroTemperatureInterbandBastinPairLimitIntegral
  apply integral_congr_ae
  have hne : ∀ᵐ p : ℝ, p ≠ pF := by
    rw [MeasureTheory.ae_iff]
    simp
  have hne' : ∀ᵐ p ∂(volume.restrict (Set.Icc (0 : ℝ) pMax)), p ≠ pF := by
    rw [ae_restrict_iff' measurableSet_Icc]
    exact hne.mono (fun p hp _ => hp)
  have hmem : ∀ᵐ p ∂(volume.restrict (Set.Icc (0 : ℝ) pMax)),
      p ∈ Set.Icc (0 : ℝ) pMax :=
    MeasureTheory.ae_restrict_mem measurableSet_Icc
  filter_upwards [hne', hmem] with p hpF hp
  exact radialZeroTemperatureInterbandBastinPairLimitDensity_eq_sharp_of_ne
    band e v m fermiEnergy p (by
      intro hfermi
      exact hpF (hfermiUnique p hp hfermi))

end

end AnomalousHall.MassiveDirac
