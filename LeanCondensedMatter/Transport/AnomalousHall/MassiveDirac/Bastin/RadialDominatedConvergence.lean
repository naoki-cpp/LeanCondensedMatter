import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Bastin.CleanConductivity
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Bastin.RadialDomination
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Bastin.RadialPairUniformBound
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Dominated convergence for the finite radial massive-Dirac Bastin integral

The clean interband Bastin-pair limit is known pointwise in radial momentum. This file packages the
finite radial densities and integrals, records the dominated-convergence boundary for passing the
positive zero-broadening limit through a finite radial integral, and discharges that boundary from
the mass-magnitude gap and uniform radial spectator bounds.

The measurability argument views the target-window pole integral as a parameter-dependent Bochner
integral of a jointly measurable radial/energy-offset integrand. The ultraviolet cutoff remains
fixed throughout; no `pMax → ∞` limit is mixed with `η → 0⁺`.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter MeasureTheory Set

/-- Radial momentum density of the finite-broadening, target-centered interband Bastin pair. The
factor `p` is the two-dimensional radial Jacobian; the angular factor remains outside this density.
-/
def radialInterbandBastinPairDensity
    (band : Band) (e v m radius p broadening : ℝ) : ℝ :=
  p * (targetCenteredInterbandBastinPairIntegral
    band e v m p 0 radius broadening).re

/-- Radial momentum density of the already-extracted clean interband Bastin-pair limit. -/
def radialCleanInterbandBastinPairLimitDensity
    (band : Band) (e v m p : ℝ) : ℝ :=
  p * cleanInterbandBastinPairLimitDensity band e v m p 0

/-- Nonzero mass makes the fixed-window pointwise Bastin-pair limit uniform whenever one radius
satisfies `radius < 2|m|` at every radial momentum. -/
theorem tendsto_radialInterbandBastinPairDensity
    (band : Band) (e v m radius p : ℝ)
    (hm : m ≠ 0) (hradiusPos : 0 < radius) (hradius : radius < 2 * |m|) :
    Tendsto
      (fun broadening : ℝ =>
        radialInterbandBastinPairDensity band e v m radius p broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (radialCleanInterbandBastinPairLimitDensity band e v m p)) := by
  have hE : energy v m p 0 ≠ 0 :=
    ne_of_gt (energy_pos_of_mass_ne_zero v m p 0 hm)
  have hgap : radius < |interbandEnergyGap band v m p 0| :=
    radius_lt_abs_interbandEnergyGap_of_lt_two_mul_abs_mass
      band v m p 0 radius hradius
  have hpair :=
    tendsto_targetCenteredInterbandBastinPairIntegral_re_cleanLimitDensity
      band e v m p 0 radius hE hradiusPos hgap
  unfold radialInterbandBastinPairDensity radialCleanInterbandBastinPairLimitDensity
  exact tendsto_const_nhds.mul hpair

/-- Finite radial momentum integral of the finite-broadening interband Bastin-pair density. -/
def finiteRadialInterbandBastinPairIntegral
    (band : Band) (e v m radius pMax broadening : ℝ) : ℝ :=
  ∫ p in Set.Icc 0 pMax,
    radialInterbandBastinPairDensity band e v m radius p broadening

/-- Finite radial momentum integral of the clean interband Bastin-pair limit density. -/
def finiteRadialCleanInterbandBastinPairIntegral
    (band : Band) (e v m pMax : ℝ) : ℝ :=
  ∫ p in Set.Icc 0 pMax,
    radialCleanInterbandBastinPairLimitDensity band e v m p

/-- Dominated convergence passes `η → 0⁺` through the finite radial momentum integral once a
single integrable radial bound and eventual measurability are supplied. The pointwise convergence
hypothesis is not repeated: it follows from nonzero mass and `radius < 2|m|`. -/
theorem tendsto_finiteRadialInterbandBastinPairIntegral_of_dominated
    (band : Band) (e v m radius pMax : ℝ)
    (hm : m ≠ 0) (hradiusPos : 0 < radius) (hradius : radius < 2 * |m|)
    (bound : ℝ → ℝ)
    (hMeasurable :
      ∀ᶠ broadening : ℝ in nhdsWithin 0 (Set.Ioi 0),
        AEStronglyMeasurable
          (fun p => radialInterbandBastinPairDensity
            band e v m radius p broadening)
          (volume.restrict (Set.Icc 0 pMax)))
    (hBound :
      ∀ᶠ broadening : ℝ in nhdsWithin 0 (Set.Ioi 0),
        ∀ᵐ p ∂(volume.restrict (Set.Icc 0 pMax)),
          ‖radialInterbandBastinPairDensity band e v m radius p broadening‖ ≤ bound p)
    (hBoundIntegrable :
      Integrable bound (volume.restrict (Set.Icc 0 pMax))) :
    Tendsto
      (fun broadening : ℝ =>
        finiteRadialInterbandBastinPairIntegral
          band e v m radius pMax broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (finiteRadialCleanInterbandBastinPairIntegral band e v m pMax)) := by
  unfold finiteRadialInterbandBastinPairIntegral finiteRadialCleanInterbandBastinPairIntegral
  exact tendsto_integral_filter_of_dominated_convergence
    bound hMeasurable hBound hBoundIntegrable
    (ae_of_all _ fun p =>
      tendsto_radialInterbandBastinPairDensity
        band e v m radius p hm hradiusPos hradius)

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
        QuantumTheory.Transport.lorentzianRegularFactorIntegral
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

/-- The model-specific positive-mass bounds discharge all hypotheses of finite-radial dominated
convergence. Thus the finite-broadening radial momentum integral converges to the integral of the
clean local limit profile as `η → 0⁺`. -/
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
  have hradiusAbs : radius < 2 * |m| := by
    simpa [abs_of_pos hm] using hradius
  apply tendsto_finiteRadialInterbandBastinPairIntegral_of_dominated
    band e v m radius pMax hm.ne' hradiusPos hradiusAbs
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
