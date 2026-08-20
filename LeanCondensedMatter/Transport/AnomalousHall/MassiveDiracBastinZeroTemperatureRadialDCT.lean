import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinZeroTemperaturePairLimit
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinRadialDominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Radial dominated convergence for the zero-temperature occupation-weighted Bastin pair

The pointwise zero-temperature weighted interband pair now has a unified clean limit carrying the
exact `π / 0 / π/2` spectral weight. The finite-broadening weighted pair also inherits the same
momentum-independent norm bound as the unweighted pair. This file supplies the remaining radial
measurability and applies dominated convergence on every finite radial interval.

The target of the limit retains the exact Fermi-surface half-weight. No measure-zero simplification
or ultraviolet limit is used here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter MeasureTheory Set

/-- Finite-broadening radial density of the zero-temperature occupation-weighted interband pair. -/
def radialZeroTemperatureInterbandBastinPairDensity
    (band : Band) (e v m fermiEnergy radius p broadening : ℝ) : ℝ :=
  p * (targetCenteredZeroTemperatureInterbandBastinPairIntegral
    band e v m p 0 fermiEnergy radius broadening).re

/-- Unified radial clean-limit density, retaining the exact half-weight at a Fermi-surface pole. -/
def radialZeroTemperatureInterbandBastinPairLimitDensity
    (band : Band) (e v m fermiEnergy p : ℝ) : ℝ :=
  p * (-2 * zeroTemperatureLorentzianPoleWeight
    fermiEnergy (bandEnergy band v m p 0) *
      (e ^ 2 * berryCurvature band v m p 0))

/-- Finite radial momentum integral of the zero-temperature weighted finite-broadening pair. -/
def finiteRadialZeroTemperatureInterbandBastinPairIntegral
    (band : Band) (e v m fermiEnergy radius pMax broadening : ℝ) : ℝ :=
  ∫ p in Set.Icc 0 pMax,
    radialZeroTemperatureInterbandBastinPairDensity
      band e v m fermiEnergy radius p broadening

/-- Finite radial momentum integral of the unified zero-temperature clean-limit density. -/
def finiteRadialZeroTemperatureInterbandBastinPairLimitIntegral
    (band : Band) (e v m fermiEnergy pMax : ℝ) : ℝ :=
  ∫ p in Set.Icc 0 pMax,
    radialZeroTemperatureInterbandBastinPairLimitDensity
      band e v m fermiEnergy p

/-- The target-centered zero-temperature occupation is jointly measurable in radial momentum and
energy offset. -/
theorem measurable_radialZeroTemperatureOccupation
    (band : Band) (v m fermiEnergy : ℝ) :
    Measurable (fun z : ℝ × ℝ =>
      zeroTemperatureOccupation fermiEnergy
        (bandEnergy band v m z.1 0 + z.2)) := by
  have henergy : Measurable (fun z : ℝ × ℝ =>
      bandEnergy band v m z.1 0 + z.2) := by
    unfold bandEnergy energy energySq
    measurability
  unfold zeroTemperatureOccupation
  exact Measurable.ite
    (measurableSet_lt henergy measurable_const)
    measurable_const measurable_const

/-- The zero-temperature occupation-weighted Lorentzian/spectator integrand is jointly strongly
measurable on the radial momentum/offset plane for fixed positive broadening. -/
theorem stronglyMeasurable_radialZeroTemperatureInterbandPoleIntegrand
    (band : Band) (e v m fermiEnergy broadening : ℝ) (hm : 0 < m) :
    StronglyMeasurable
      (fun z : ℝ × ℝ =>
        ((zeroTemperatureOccupation fermiEnergy
          (bandEnergy band v m z.1 0 + z.2) : ℝ) : ℂ) *
          ((lorentzianSpectralKernel z.2 broadening : ℂ) *
            targetCenteredInterbandSpectatorCurrentFactor
              band e v m z.1 0 (z.2, broadening))) := by
  have hocc : StronglyMeasurable (fun z : ℝ × ℝ =>
      ((zeroTemperatureOccupation fermiEnergy
        (bandEnergy band v m z.1 0 + z.2) : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.measurable.comp
      (measurable_radialZeroTemperatureOccupation band v m fermiEnergy)).stronglyMeasurable
  exact hocc.mul (stronglyMeasurable_radialInterbandPoleIntegrand
    band e v m broadening hm)

/-- For positive broadening the zero-temperature weighted target-centered pair is strongly
measurable as a function of radial momentum. -/
theorem stronglyMeasurable_targetCenteredZeroTemperatureInterbandBastinPairIntegral_radial
    (band : Band) (e v m fermiEnergy radius broadening : ℝ)
    (hm : 0 < m) (hradiusPos : 0 < radius) (hbroadening : 0 < broadening) :
    StronglyMeasurable
      (fun p : ℝ =>
        targetCenteredZeroTemperatureInterbandBastinPairIntegral
          band e v m p 0 fermiEnergy radius broadening) := by
  have hab : -radius ≤ radius := by linarith
  let F : ℝ × ℝ → ℂ := fun z =>
    ((zeroTemperatureOccupation fermiEnergy
      (bandEnergy band v m z.1 0 + z.2) : ℝ) : ℂ) *
      ((lorentzianSpectralKernel z.2 broadening : ℂ) *
        targetCenteredInterbandSpectatorCurrentFactor
          band e v m z.1 0 (z.2, broadening))
  have hF : StronglyMeasurable F := by
    dsimp [F]
    exact stronglyMeasurable_radialZeroTemperatureInterbandPoleIntegrand
      band e v m fermiEnergy broadening hm
  have hparam : StronglyMeasurable
      (fun p : ℝ =>
        ∫ offset : ℝ, F (p, offset) ∂(volume.restrict (Set.Ioc (-radius) radius))) :=
    hF.integral_prod_right'
  have hpole : StronglyMeasurable
      (fun p : ℝ =>
        targetCenteredZeroTemperatureInterbandSpectatorCurrentPoleIntegral
          band e v m p 0 fermiEnergy radius broadening) := by
    have heq :
        (fun p : ℝ =>
          targetCenteredZeroTemperatureInterbandSpectatorCurrentPoleIntegral
            band e v m p 0 fermiEnergy radius broadening) =
        (fun p : ℝ =>
          ∫ offset : ℝ, F (p, offset) ∂(volume.restrict (Set.Ioc (-radius) radius))) := by
      funext p
      unfold targetCenteredZeroTemperatureInterbandSpectatorCurrentPoleIntegral
      rw [intervalIntegral.integral_of_le hab]
    rw [heq]
    exact hparam
  have hscaled := hpole.const_mul (-2 * Complex.I : ℂ)
  have heqPair :
      (fun p : ℝ =>
        targetCenteredZeroTemperatureInterbandBastinPairIntegral
          band e v m p 0 fermiEnergy radius broadening) =
      (fun p : ℝ =>
        (-2 * Complex.I) *
          targetCenteredZeroTemperatureInterbandSpectatorCurrentPoleIntegral
            band e v m p 0 fermiEnergy radius broadening) := by
    funext p
    exact targetCenteredZeroTemperatureInterbandBastinPairIntegral_eq_neg_two_i_mul_poleIntegral
      band e v m p 0 fermiEnergy radius broadening hbroadening.ne'
  rw [heqPair]
  exact hscaled

/-- The real zero-temperature weighted radial pair density is strongly measurable for positive
broadening. -/
theorem stronglyMeasurable_radialZeroTemperatureInterbandBastinPairDensity
    (band : Band) (e v m fermiEnergy radius broadening : ℝ)
    (hm : 0 < m) (hradiusPos : 0 < radius) (hbroadening : 0 < broadening) :
    StronglyMeasurable
      (fun p : ℝ =>
        radialZeroTemperatureInterbandBastinPairDensity
          band e v m fermiEnergy radius p broadening) := by
  have hpair :=
    stronglyMeasurable_targetCenteredZeroTemperatureInterbandBastinPairIntegral_radial
      band e v m fermiEnergy radius broadening hm hradiusPos hbroadening
  have hre : StronglyMeasurable
      (fun p : ℝ =>
        (targetCenteredZeroTemperatureInterbandBastinPairIntegral
          band e v m p 0 fermiEnergy radius broadening).re) := by
    exact Complex.continuous_re.comp_stronglyMeasurable hpair
  unfold radialZeroTemperatureInterbandBastinPairDensity
  exact stronglyMeasurable_id.mul hre

/-- Positive mass and one fixed window give pointwise convergence of the weighted radial pair at
every radial momentum, including the exact Fermi-surface half-weight. -/
theorem tendsto_radialZeroTemperatureInterbandBastinPairDensity
    (band : Band) (e v m fermiEnergy radius p : ℝ)
    (hm : 0 < m) (hradiusPos : 0 < radius) (hradius : radius < 2 * m) :
    Tendsto
      (fun broadening : ℝ =>
        radialZeroTemperatureInterbandBastinPairDensity
          band e v m fermiEnergy radius p broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (radialZeroTemperatureInterbandBastinPairLimitDensity
        band e v m fermiEnergy p)) := by
  have hE : energy v m p 0 ≠ 0 :=
    ne_of_gt (energy_pos_of_mass_pos v m p 0 hm)
  have hgap : radius < |interbandEnergyGap band v m p 0| :=
    radius_lt_abs_interbandEnergyGap_of_lt_two_mul_mass
      band v m p 0 radius hm hradius
  have hpair :=
    tendsto_targetCenteredZeroTemperatureInterbandBastinPairIntegral_re
      band e v m p 0 fermiEnergy radius hE hradiusPos hgap
  unfold radialZeroTemperatureInterbandBastinPairDensity
    radialZeroTemperatureInterbandBastinPairLimitDensity
  exact tendsto_const_nhds.mul hpair

/-- The same constant used in the unweighted radial DCT dominates the zero-temperature weighted
radial pair density on every finite radial interval. -/
theorem norm_radialZeroTemperatureInterbandBastinPairDensity_le_dominatingConstant
    (band : Band) (e v m fermiEnergy radius pMax p broadening : ℝ)
    (hm : 0 < m) (hradiusPos : 0 < radius) (hradius : radius < 2 * m)
    (hp : p ∈ Set.Icc (0 : ℝ) pMax) (hbroadening : 0 < broadening) :
    ‖radialZeroTemperatureInterbandBastinPairDensity
        band e v m fermiEnergy radius p broadening‖ ≤
      radialInterbandBastinDominatingConstant e v m radius pMax := by
  have hpair := norm_targetCenteredZeroTemperatureInterbandBastinPairIntegral_radial_le
    band e v m p fermiEnergy radius broadening hm hradiusPos hradius hbroadening
  have hre := Complex.abs_re_le_norm
    (targetCenteredZeroTemperatureInterbandBastinPairIntegral
      band e v m p 0 fermiEnergy radius broadening)
  have hpair' :
      ‖targetCenteredZeroTemperatureInterbandBastinPairIntegral
          band e v m p 0 fermiEnergy radius broadening‖ ≤
        radialInterbandBastinPairUniformBound e v m radius := by
    simpa [radialInterbandBastinPairUniformBound] using hpair
  have hre' :
      |(targetCenteredZeroTemperatureInterbandBastinPairIntegral
          band e v m p 0 fermiEnergy radius broadening).re| ≤
        radialInterbandBastinPairUniformBound e v m radius :=
    hre.trans hpair'
  have hB := radialInterbandBastinPairUniformBound_nonneg e v m radius
  unfold radialZeroTemperatureInterbandBastinPairDensity
    radialInterbandBastinDominatingConstant
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp.1]
  calc
    p * |(targetCenteredZeroTemperatureInterbandBastinPairIntegral
        band e v m p 0 fermiEnergy radius broadening).re| ≤
      p * radialInterbandBastinPairUniformBound e v m radius :=
        mul_le_mul_of_nonneg_left hre' hp.1
    _ ≤ pMax * radialInterbandBastinPairUniformBound e v m radius :=
      mul_le_mul_of_nonneg_right hp.2 hB

/-- Dominated convergence passes the physical zero-temperature weighted pair through every finite
radial momentum integral. -/
theorem tendsto_finiteRadialZeroTemperatureInterbandBastinPairIntegral
    (band : Band) (e v m fermiEnergy radius pMax : ℝ)
    (hm : 0 < m) (hpMax : 0 ≤ pMax)
    (hradiusPos : 0 < radius) (hradius : radius < 2 * m) :
    Tendsto
      (fun broadening : ℝ =>
        finiteRadialZeroTemperatureInterbandBastinPairIntegral
          band e v m fermiEnergy radius pMax broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (finiteRadialZeroTemperatureInterbandBastinPairLimitIntegral
        band e v m fermiEnergy pMax)) := by
  unfold finiteRadialZeroTemperatureInterbandBastinPairIntegral
    finiteRadialZeroTemperatureInterbandBastinPairLimitIntegral
  exact tendsto_integral_filter_of_dominated_convergence
    (fun _ : ℝ => radialInterbandBastinDominatingConstant e v m radius pMax)
    (by
      filter_upwards [self_mem_nhdsWithin] with broadening hbroadening
      exact (stronglyMeasurable_radialZeroTemperatureInterbandBastinPairDensity
        band e v m fermiEnergy radius broadening hm hradiusPos hbroadening).aestronglyMeasurable)
    (by
      filter_upwards [self_mem_nhdsWithin] with broadening hbroadening
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun p hp =>
        norm_radialZeroTemperatureInterbandBastinPairDensity_le_dominatingConstant
          band e v m fermiEnergy radius pMax p broadening
          hm hradiusPos hradius hp hbroadening))
    (integrable_radialInterbandBastinDominatingConstant e v m radius pMax hpMax)
    (ae_of_all _ fun p =>
      tendsto_radialZeroTemperatureInterbandBastinPairDensity
        band e v m fermiEnergy radius p hm hradiusPos hradius)

end

end AnomalousHall.MassiveDirac
