import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Bastin.RadialLimitInterchange
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Bastin.RadialPairUniformBound
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Model-specific dominated convergence for the finite radial Bastin integral

The preceding radial estimates give a momentum- and broadening-independent norm bound for the
energy-integrated interband Bastin pair.  On a finite radial interval `0 ≤ p ≤ pMax`, multiplication
by the radial Jacobian `p` is therefore dominated by one constant integrable function.

This file also discharges the remaining measurability hypothesis by viewing the target-window pole
integral as a parameter-dependent Bochner integral of a jointly measurable radial/energy-offset
integrand.  The generic dominated-convergence theorem from `MassiveDiracBastinRadialLimitInterchange`
then yields the actual finite-broadening radial limit interchange.

The ultraviolet cutoff remains fixed throughout.  No `pMax → ∞` limit is mixed with `η → 0⁺`.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter MeasureTheory Set

/-- Uniform norm bound for the complete energy-integrated radial Bastin pair. -/
def radialInterbandBastinPairUniformBound
    (e v m radius : ℝ) : ℝ :=
  2 * (radialInterbandSpectatorUniformBound e v m radius * Real.pi)

/-- The pair bound is nonnegative. -/
theorem radialInterbandBastinPairUniformBound_nonneg
    (e v m radius : ℝ) :
    0 ≤ radialInterbandBastinPairUniformBound e v m radius := by
  unfold radialInterbandBastinPairUniformBound
  have hC := radialInterbandSpectatorUniformBound_nonneg e v m radius
  have hpi := Real.pi_pos.le
  positivity

/-- Constant dominating function after attaching the radial Jacobian on `0 ≤ p ≤ pMax`. -/
def radialInterbandBastinDominatingConstant
    (e v m radius pMax : ℝ) : ℝ :=
  pMax * radialInterbandBastinPairUniformBound e v m radius

/-- The radial dominating constant is nonnegative for a nonnegative radial cutoff. -/
theorem radialInterbandBastinDominatingConstant_nonneg
    (e v m radius pMax : ℝ) (hpMax : 0 ≤ pMax) :
    0 ≤ radialInterbandBastinDominatingConstant e v m radius pMax := by
  unfold radialInterbandBastinDominatingConstant
  exact mul_nonneg hpMax (radialInterbandBastinPairUniformBound_nonneg e v m radius)

/-- Joint strong measurability of the Lorentzian-weighted radial spectator integrand for every
strictly positive broadening. -/
theorem stronglyMeasurable_radialInterbandPoleIntegrand
    (band : Band) (e v m broadening : ℝ) (hm : 0 < m) :
    StronglyMeasurable
      (fun z : ℝ × ℝ =>
        (lorentzianSpectralKernel z.2 broadening : ℂ) *
          targetCenteredInterbandSpectatorCurrentFactor
            band e v m z.1 0 (z.2, broadening)) := by
  have hfun :
      (fun z : ℝ × ℝ =>
        (lorentzianSpectralKernel z.2 broadening : ℂ) *
          targetCenteredInterbandSpectatorCurrentFactor
            band e v m z.1 0 (z.2, broadening)) =
      (fun z : ℝ × ℝ =>
        (lorentzianSpectralKernel z.2 broadening : ℂ) *
          (((((interbandEnergyGap band v m z.1 0 + z.2 : ℝ) : ℂ) +
              (broadening : ℂ) * Complex.I)⁻¹) ^ 2 +
            ((((interbandEnergyGap band v m z.1 0 + z.2 : ℝ) : ℂ) -
              (broadening : ℂ) * Complex.I)⁻¹) ^ 2) *
            radialInterbandCurrentAmplitude band e v m z.1) := by
    funext z
    rw [targetCenteredInterbandSpectatorCurrentFactor_radial_eq
      band e v m z.1 z.2 broadening
      (ne_of_gt (energy_pos_of_mass_pos v m z.1 0 hm))]
    ring
  rw [hfun]
  apply Measurable.stronglyMeasurable
  unfold lorentzianSpectralKernel QuantumTheory.Transport.lorentzianSpectralKernel
    radialInterbandCurrentAmplitude interbandEnergyGap bandEnergy energy energySq
  measurability

/-- For positive broadening the radial target-centered Bastin pair is strongly measurable as a
function of radial momentum. -/
theorem stronglyMeasurable_targetCenteredInterbandBastinPairIntegral_radial
    (band : Band) (e v m radius broadening : ℝ)
    (hm : 0 < m) (hradiusPos : 0 < radius) (hbroadening : 0 < broadening) :
    StronglyMeasurable
      (fun p : ℝ =>
        targetCenteredInterbandBastinPairIntegral
          band e v m p 0 radius broadening) := by
  have hab : -radius ≤ radius := by linarith
  let F : ℝ × ℝ → ℂ := fun z =>
    (lorentzianSpectralKernel z.2 broadening : ℂ) *
      targetCenteredInterbandSpectatorCurrentFactor
        band e v m z.1 0 (z.2, broadening)
  have hF : StronglyMeasurable F := by
    dsimp [F]
    exact stronglyMeasurable_radialInterbandPoleIntegrand
      band e v m broadening hm
  have hparam : StronglyMeasurable
      (fun p : ℝ =>
        ∫ offset : ℝ, F (p, offset) ∂(volume.restrict (Set.Ioc (-radius) radius))) :=
    hF.integral_prod_right'
  have hpole : StronglyMeasurable
      (fun p : ℝ =>
        targetCenteredInterbandSpectatorCurrentPoleIntegral
          band e v m p 0 radius broadening) := by
    have heq :
        (fun p : ℝ =>
          targetCenteredInterbandSpectatorCurrentPoleIntegral
            band e v m p 0 radius broadening) =
        (fun p : ℝ =>
          ∫ offset : ℝ, F (p, offset) ∂(volume.restrict (Set.Ioc (-radius) radius))) := by
      funext p
      unfold targetCenteredInterbandSpectatorCurrentPoleIntegral
      rw [intervalIntegral.integral_of_le hab]
    rw [heq]
    exact hparam
  have hscaled := hpole.const_mul (-2 * Complex.I : ℂ)
  have heqPair :
      (fun p : ℝ =>
        targetCenteredInterbandBastinPairIntegral
          band e v m p 0 radius broadening) =
      (fun p : ℝ =>
        (-2 * Complex.I) *
          targetCenteredInterbandSpectatorCurrentPoleIntegral
            band e v m p 0 radius broadening) := by
    funext p
    exact targetCenteredInterbandBastinPairIntegral_eq_neg_two_i_mul_poleIntegral
      band e v m p 0 radius broadening hbroadening.ne'
  rw [heqPair]
  exact hscaled

/-- The real radial Bastin density is strongly measurable for positive broadening. -/
theorem stronglyMeasurable_radialInterbandBastinPairDensity
    (band : Band) (e v m radius broadening : ℝ)
    (hm : 0 < m) (hradiusPos : 0 < radius) (hbroadening : 0 < broadening) :
    StronglyMeasurable
      (fun p : ℝ =>
        radialInterbandBastinPairDensity
          band e v m radius p broadening) := by
  have hpair :=
    stronglyMeasurable_targetCenteredInterbandBastinPairIntegral_radial
      band e v m radius broadening hm hradiusPos hbroadening
  have hre : StronglyMeasurable
      (fun p : ℝ =>
        (targetCenteredInterbandBastinPairIntegral
          band e v m p 0 radius broadening).re) := by
    exact Complex.continuous_re.comp_stronglyMeasurable hpair
  unfold radialInterbandBastinPairDensity
  exact stronglyMeasurable_id.mul hre

/-- The explicit radial constant dominates the finite-broadening radial Bastin density pointwise on
`0 ≤ p ≤ pMax`. -/
theorem norm_radialInterbandBastinPairDensity_le_dominatingConstant
    (band : Band) (e v m radius pMax p broadening : ℝ)
    (hm : 0 < m) (hradiusPos : 0 < radius) (hradius : radius < 2 * m)
    (hp : p ∈ Set.Icc (0 : ℝ) pMax) (hbroadening : 0 < broadening) :
    ‖radialInterbandBastinPairDensity
        band e v m radius p broadening‖ ≤
      radialInterbandBastinDominatingConstant e v m radius pMax := by
  have hpair := norm_targetCenteredInterbandBastinPairIntegral_radial_le
    band e v m p radius broadening hm hradiusPos hradius hbroadening
  have hre := Complex.abs_re_le_norm
    (targetCenteredInterbandBastinPairIntegral
      band e v m p 0 radius broadening)
  have hpair' :
      ‖targetCenteredInterbandBastinPairIntegral
          band e v m p 0 radius broadening‖ ≤
        radialInterbandBastinPairUniformBound e v m radius := by
    simpa [radialInterbandBastinPairUniformBound] using hpair
  have hre' :
      |(targetCenteredInterbandBastinPairIntegral
          band e v m p 0 radius broadening).re| ≤
        radialInterbandBastinPairUniformBound e v m radius :=
    hre.trans hpair'
  have hB := radialInterbandBastinPairUniformBound_nonneg e v m radius
  unfold radialInterbandBastinPairDensity radialInterbandBastinDominatingConstant
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp.1]
  calc
    p * |(targetCenteredInterbandBastinPairIntegral
        band e v m p 0 radius broadening).re| ≤
      p * radialInterbandBastinPairUniformBound e v m radius :=
        mul_le_mul_of_nonneg_left hre' hp.1
    _ ≤ pMax * radialInterbandBastinPairUniformBound e v m radius :=
      mul_le_mul_of_nonneg_right hp.2 hB

/-- The constant dominating function is integrable on every finite radial interval. -/
theorem integrable_radialInterbandBastinDominatingConstant
    (e v m radius pMax : ℝ) (hpMax : 0 ≤ pMax) :
    Integrable
      (fun _ : ℝ => radialInterbandBastinDominatingConstant e v m radius pMax)
      (volume.restrict (Set.Icc 0 pMax)) := by
  have hD := radialInterbandBastinDominatingConstant_nonneg
    e v m radius pMax hpMax
  refine MeasureTheory.IntegrableOn.of_bound
    isCompact_Icc.measure_lt_top
    (aestronglyMeasurable_const)
    (radialInterbandBastinDominatingConstant e v m radius pMax) ?_
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun _ _ => by
    simp [Real.norm_eq_abs, abs_of_nonneg hD])

/-- The model-specific positive-mass bounds discharge all hypotheses of the finite-radial dominated
convergence theorem.  Thus the actual finite-broadening radial momentum integral converges to the
integral of the clean local limit profile as `η → 0⁺`. -/
theorem tendsto_finiteRadialInterbandBastinPairIntegral
    (band : Band) (e v m radius pMax : ℝ)
    (hm : 0 < m) (hpMax : 0 ≤ pMax)
    (hradiusPos : 0 < radius) (hradius : radius < 2 * m) :
    Tendsto
      (fun broadening : ℝ =>
        finiteRadialInterbandBastinPairIntegral
          band e v m radius pMax broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (finiteRadialCleanInterbandBastinPairIntegral band e v m pMax)) := by
  apply tendsto_finiteRadialInterbandBastinPairIntegral_of_dominated
    band e v m radius pMax hm hradiusPos hradius
    (fun _ : ℝ => radialInterbandBastinDominatingConstant e v m radius pMax)
  · filter_upwards [self_mem_nhdsWithin] with broadening hbroadening
    exact (stronglyMeasurable_radialInterbandBastinPairDensity
      band e v m radius broadening hm hradiusPos hbroadening).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with broadening hbroadening
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun p hp =>
      norm_radialInterbandBastinPairDensity_le_dominatingConstant
        band e v m radius pMax p broadening hm hradiusPos hradius hp hbroadening)
  · exact integrable_radialInterbandBastinDominatingConstant
      e v m radius pMax hpMax

end

end AnomalousHall.MassiveDirac
