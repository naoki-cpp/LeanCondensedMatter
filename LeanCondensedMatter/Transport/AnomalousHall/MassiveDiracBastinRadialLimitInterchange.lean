import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinCleanConductivity
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinRadialDomination
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite radial limit interchange for the massive-Dirac Bastin pair

The clean interband Bastin-pair limit is already known pointwise in momentum.  This file packages
that pointwise statement in the radial momentum variable and records the exact dominated-convergence
boundary needed to pass the positive zero-broadening limit through a finite radial momentum
integral.

The theorem here deliberately keeps the domination and measurability hypotheses explicit.  The
model-specific task left to the next layer is to discharge them from the positive mass gap and the
uniform radial spectator bounds prepared upstream.  No ultraviolet limit is mixed into this step.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter MeasureTheory Set

/-- Radial momentum density of the finite-broadening, target-centered interband Bastin pair.  The
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

/-- Positive mass makes the fixed-window pointwise Bastin-pair limit uniform in the sense that one
radius satisfying `radius < 2m` is valid at every radial momentum. -/
theorem tendsto_radialInterbandBastinPairDensity
    (band : Band) (e v m radius p : ℝ)
    (hm : 0 < m) (hradiusPos : 0 < radius) (hradius : radius < 2 * m) :
    Tendsto
      (fun broadening : ℝ =>
        radialInterbandBastinPairDensity band e v m radius p broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (radialCleanInterbandBastinPairLimitDensity band e v m p)) := by
  have hE : energy v m p 0 ≠ 0 :=
    ne_of_gt (energy_pos_of_mass_pos v m p 0 hm)
  have hgap : radius < |interbandEnergyGap band v m p 0| :=
    radius_lt_abs_interbandEnergyGap_of_lt_two_mul_mass
      band v m p 0 radius hm hradius
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
single integrable radial bound and eventual measurability are supplied.  The pointwise convergence
hypothesis is not repeated: it follows from the positive mass gap and `radius < 2m`. -/
theorem tendsto_finiteRadialInterbandBastinPairIntegral_of_dominated
    (band : Band) (e v m radius pMax : ℝ)
    (hm : 0 < m) (hradiusPos : 0 < radius) (hradius : radius < 2 * m)
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

end

end AnomalousHall.MassiveDirac
