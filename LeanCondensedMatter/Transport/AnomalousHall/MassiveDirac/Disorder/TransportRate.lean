import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.SingleParticleRate
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Model.FermiSurfaceKinematics
import LeanCondensedMatter.Transport.Analysis.RelaxationTime
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Metallic upper-band Born transport scattering rate

This module separates the current-relaxation scale from the already-derived single-particle Born
lifetime.  For scalar short-range disorder, the same upper-band Born scattering kernel is weighted
by the gauge-independent band-projector overlap on the isotropic Fermi circle.  The
single-particle rate uses the unweighted angular average, whereas current relaxation carries the
additional factor `1 - cos θ`.

For `0 < m < ε_F`, the upper-band projector overlap reduces to

```text
W(θ) = [1 + m²/ε_F² + (1 - m²/ε_F²) cos θ] / 2.
```

Hence

```text
<W> = (1 + m²/ε_F²) / 2,
<W (1 - cos θ)> = (1 + 3 m²/ε_F²) / 4.
```

The transport rate is normalized by the same continuum Born prefactor already fixed by the
microscopic single-particle self-energy.  No Kubo ladder equation, Ward identity, crossed diagram,
or identification with the exact disorder-averaged conductivity is claimed here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport
open scoped Interval

private theorem energy_polar_eq_radial
    (v m p θ : ℝ) :
    energy v m (p * Real.cos θ) (p * Real.sin θ) = energy v m p 0 := by
  unfold energy energySq
  congr 1
  have htrig : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  calc
    v ^ 2 * ((p * Real.cos θ) ^ 2 + (p * Real.sin θ) ^ 2) + m ^ 2 =
        v ^ 2 * (p ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2)) + m ^ 2 := by ring
    _ = v ^ 2 * (p ^ 2 * 1) + m ^ 2 := by rw [htrig]
    _ = v ^ 2 * (p ^ 2 + 0 ^ 2) + m ^ 2 := by ring

private theorem upperBandProjectorOverlap_re_eq
    (v m px py qx qy : ℝ)
    (hp : energy v m px py ≠ 0) (hq : energy v m qx qy ≠ 0) :
    (Matrix.trace
      (bandProjector .upper v m px py * bandProjector .upper v m qx qy)).re =
      (1 +
        (v ^ 2 * (px * qx + py * qy) + m ^ 2) /
          (energy v m px py * energy v m qx qy)) / 2 := by
  simp [bandProjector, Matrix.trace, Matrix.mul_apply, hamiltonian,
    sigmaX, sigmaY, sigmaZ]
  field_simp [hp, hq]
  ring

/-- Gauge-independent scalar-disorder overlap weight between an upper-band state chosen on the
positive `p_x` axis and a state at relative Fermi-circle angle `θ`.  For rank-one projectors this is
`Tr(P_+(p) P_+(p')) = |<u_p'|u_p>|²`. -/
def upperBandFermiSurfaceScalarOverlapWeight
    (v m fermiEnergy θ : ℝ) : ℝ :=
  let pF := metallicFermiRadius v m fermiEnergy
  (Matrix.trace
    (bandProjector .upper v m pF 0 *
      bandProjector .upper v m (pF * Real.cos θ) (pF * Real.sin θ))).re

/-- Closed upper-band scalar-disorder overlap on the metallic Fermi circle. -/
theorem upperBandFermiSurfaceScalarOverlapWeight_eq
    (v m fermiEnergy θ : ℝ) (hv : v ≠ 0)
    (hm : 0 < m) (hmF : m ≤ fermiEnergy) :
    upperBandFermiSurfaceScalarOverlapWeight v m fermiEnergy θ =
      (1 + m ^ 2 / fermiEnergy ^ 2 +
        (1 - m ^ 2 / fermiEnergy ^ 2) * Real.cos θ) / 2 := by
  have hfermiPos : 0 < fermiEnergy := lt_of_lt_of_le hm hmF
  have hfermiNe : fermiEnergy ≠ 0 := ne_of_gt hfermiPos
  have hE := energy_metallicFermiRadius v m fermiEnergy hv hm hmF
  have hENe : energy v m (metallicFermiRadius v m fermiEnergy) 0 ≠ 0 := by
    rw [hE]
    exact hfermiNe
  unfold upperBandFermiSurfaceScalarOverlapWeight
  rw [upperBandProjectorOverlap_re_eq]
  · rw [energy_polar_eq_radial, hE]
    have hpFproduct :
        metallicFermiRadius v m fermiEnergy *
              (metallicFermiRadius v m fermiEnergy * Real.cos θ) +
            0 * (metallicFermiRadius v m fermiEnergy * Real.sin θ) =
          metallicFermiRadius v m fermiEnergy ^ 2 * Real.cos θ := by
      ring
    rw [hpFproduct, metallicFermiRadius_sq v m fermiEnergy hm hmF]
    field_simp [hfermiNe, hv] <;> ring
  · exact hENe
  · rw [energy_polar_eq_radial]
    exact hENe

private theorem integral_cos_sq_zero_two_pi :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), Real.cos θ ^ 2) = Real.pi := by
  have hcos :
      IntervalIntegrable (fun θ : ℝ => Real.cos θ ^ 2) volume 0 (2 * Real.pi) :=
    (Real.continuous_cos.pow 2).intervalIntegrable 0 (2 * Real.pi)
  have hsin :
      IntervalIntegrable (fun θ : ℝ => Real.sin θ ^ 2) volume 0 (2 * Real.pi) :=
    (Real.continuous_sin.pow 2).intervalIntegrable 0 (2 * Real.pi)
  have hdiff :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), Real.cos θ ^ 2) -
          (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), Real.sin θ ^ 2) = 0 := by
    rw [← intervalIntegral.integral_sub hcos hsin]
    simpa using
      (integral_cos_sq_sub_sin_sq (a := (0 : ℝ)) (b := 2 * Real.pi))
  have hsum :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), Real.cos θ ^ 2) +
          (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), Real.sin θ ^ 2) = 2 * Real.pi := by
    rw [← intervalIntegral.integral_add hcos hsin]
    calc
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), Real.cos θ ^ 2 + Real.sin θ ^ 2) =
          ∫ _θ : ℝ in (0 : ℝ)..(2 * Real.pi), (1 : ℝ) := by
            apply intervalIntegral.integral_congr
            intro θ _
            nlinarith [Real.sin_sq_add_cos_sq θ]
      _ = 2 * Real.pi := by simp
  linarith

/-- Full-circle mean of the upper-band scalar-disorder overlap.  This is the angular factor carried
by the single-particle Born rate. -/
def isotropicUpperBandSingleParticleAngularWeight
    (v m fermiEnergy : ℝ) : ℝ :=
  (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      upperBandFermiSurfaceScalarOverlapWeight v m fermiEnergy θ) /
    (2 * Real.pi)

/-- The unweighted scalar-disorder overlap average is `(1 + m²/ε_F²)/2`. -/
theorem isotropicUpperBandSingleParticleAngularWeight_eq
    (v m fermiEnergy : ℝ) (hv : v ≠ 0)
    (hm : 0 < m) (hmF : m ≤ fermiEnergy) :
    isotropicUpperBandSingleParticleAngularWeight v m fermiEnergy =
      (1 + m ^ 2 / fermiEnergy ^ 2) / 2 := by
  rw [isotropicUpperBandSingleParticleAngularWeight]
  have hrewrite :
      (fun θ : ℝ => upperBandFermiSurfaceScalarOverlapWeight v m fermiEnergy θ) =
        fun θ : ℝ =>
          (1 + m ^ 2 / fermiEnergy ^ 2) / 2 +
            ((1 - m ^ 2 / fermiEnergy ^ 2) / 2) * Real.cos θ := by
    funext θ
    rw [upperBandFermiSurfaceScalarOverlapWeight_eq v m fermiEnergy θ hv hm hmF]
    ring
  rw [hrewrite]
  have hconst :
      IntervalIntegrable
        (fun _θ : ℝ => (1 + m ^ 2 / fermiEnergy ^ 2) / 2) volume 0 (2 * Real.pi) :=
    continuous_const.intervalIntegrable 0 (2 * Real.pi)
  have hcos :
      IntervalIntegrable
        (fun θ : ℝ => ((1 - m ^ 2 / fermiEnergy ^ 2) / 2) * Real.cos θ)
        volume 0 (2 * Real.pi) :=
    (continuous_const.mul Real.continuous_cos).intervalIntegrable 0 (2 * Real.pi)
  rw [intervalIntegral.integral_add hconst hcos]
  rw [intervalIntegral.integral_const_mul]
  rw [integral_cos]
  simp
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hpi]

/-- Full-circle transport angular weight.  The factor `1 - cos θ` suppresses forward scattering
because it does not relax the current direction. -/
def isotropicUpperBandTransportAngularWeight
    (v m fermiEnergy : ℝ) : ℝ :=
  (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      upperBandFermiSurfaceScalarOverlapWeight v m fermiEnergy θ *
        (1 - Real.cos θ)) /
    (2 * Real.pi)

/-- The scalar-disorder transport angular weight is `(1 + 3 m²/ε_F²)/4`. -/
theorem isotropicUpperBandTransportAngularWeight_eq
    (v m fermiEnergy : ℝ) (hv : v ≠ 0)
    (hm : 0 < m) (hmF : m ≤ fermiEnergy) :
    isotropicUpperBandTransportAngularWeight v m fermiEnergy =
      (1 + 3 * (m ^ 2 / fermiEnergy ^ 2)) / 4 := by
  rw [isotropicUpperBandTransportAngularWeight]
  have hrewrite :
      (fun θ : ℝ =>
        upperBandFermiSurfaceScalarOverlapWeight v m fermiEnergy θ *
          (1 - Real.cos θ)) =
        fun θ : ℝ =>
          (1 + m ^ 2 / fermiEnergy ^ 2) / 2 -
            (m ^ 2 / fermiEnergy ^ 2) * Real.cos θ -
              ((1 - m ^ 2 / fermiEnergy ^ 2) / 2) * Real.cos θ ^ 2 := by
    funext θ
    rw [upperBandFermiSurfaceScalarOverlapWeight_eq v m fermiEnergy θ hv hm hmF]
    ring
  rw [hrewrite]
  have hconst :
      IntervalIntegrable
        (fun _θ : ℝ => (1 + m ^ 2 / fermiEnergy ^ 2) / 2) volume 0 (2 * Real.pi) :=
    continuous_const.intervalIntegrable 0 (2 * Real.pi)
  have hcos :
      IntervalIntegrable
        (fun θ : ℝ => (m ^ 2 / fermiEnergy ^ 2) * Real.cos θ)
        volume 0 (2 * Real.pi) :=
    (continuous_const.mul Real.continuous_cos).intervalIntegrable 0 (2 * Real.pi)
  have hcosSq :
      IntervalIntegrable
        (fun θ : ℝ => ((1 - m ^ 2 / fermiEnergy ^ 2) / 2) * Real.cos θ ^ 2)
        volume 0 (2 * Real.pi) :=
    (continuous_const.mul (Real.continuous_cos.pow 2)).intervalIntegrable 0 (2 * Real.pi)
  rw [intervalIntegral.integral_sub (hconst.sub hcos) hcosSq,
    intervalIntegral.integral_sub hconst hcos]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [integral_cos, integral_cos_sq_zero_two_pi]
  simp
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hpi]
  ring

/-- Common continuum Born Fermi-circle rate prefactor after isolating the dimensionless projector
angular weight.  Its normalization is checked below against the already-derived self-energy rate. -/
def continuumBornUpperBandFermiCircleRatePrefactor
    (v fermiEnergy disorderStrength hbar : ℝ) : ℝ :=
  disorderStrength * fermiEnergy / (hbar ^ 3 * v ^ 2)

/-- The microscopic single-particle rate factorizes into the common Fermi-circle prefactor and the
unweighted projector-overlap average. -/
theorem continuumBornUpperBandSingleParticleScatteringRate_eq_prefactor_mul_angularWeight
    (v m fermiEnergy disorderStrength hbar : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hm : 0 < m) (hmF : m < fermiEnergy) :
    continuumBornUpperBandSingleParticleScatteringRate
        v m fermiEnergy disorderStrength hbar =
      continuumBornUpperBandFermiCircleRatePrefactor
          v fermiEnergy disorderStrength hbar *
        isotropicUpperBandSingleParticleAngularWeight v m fermiEnergy := by
  rw [continuumBornUpperBandSingleParticleScatteringRate_eq
    v m fermiEnergy disorderStrength hbar hvelocity hhbar hm hmF]
  rw [isotropicUpperBandSingleParticleAngularWeight_eq
    v m fermiEnergy hvelocity hm hmF.le]
  unfold continuumBornUpperBandFermiCircleRatePrefactor
  have hfermiNe : fermiEnergy ≠ 0 := ne_of_gt (lt_trans hm hmF)
  field_simp [hvelocity, hhbar, hfermiNe]

/-- Upper-band Born transport scattering rate obtained from the same microscopic scalar-disorder
normalization as `1/τ_sp`, but with the current-relaxing `1 - cos θ` angular weight. -/
def continuumBornUpperBandTransportScatteringRate
    (v m fermiEnergy disorderStrength hbar : ℝ) : ℝ :=
  continuumBornUpperBandFermiCircleRatePrefactor
      v fermiEnergy disorderStrength hbar *
    isotropicUpperBandTransportAngularWeight v m fermiEnergy

/-- Closed physical-momentum expression for the upper-band Born transport scattering rate. -/
theorem continuumBornUpperBandTransportScatteringRate_eq
    (v m fermiEnergy disorderStrength hbar : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hm : 0 < m) (hmF : m < fermiEnergy) :
    continuumBornUpperBandTransportScatteringRate
        v m fermiEnergy disorderStrength hbar =
      disorderStrength / (4 * hbar ^ 3 * v ^ 2) *
        (fermiEnergy + 3 * m ^ 2 / fermiEnergy) := by
  rw [continuumBornUpperBandTransportScatteringRate,
    isotropicUpperBandTransportAngularWeight_eq
      v m fermiEnergy hvelocity hm hmF.le]
  unfold continuumBornUpperBandFermiCircleRatePrefactor
  have hfermiNe : fermiEnergy ≠ 0 := ne_of_gt (lt_trans hm hmF)
  field_simp [hvelocity, hhbar, hfermiNe]

/-- The Born transport scattering rate is positive for positive disorder strength and positive
`ℏ` in the strict metallic regime. -/
theorem continuumBornUpperBandTransportScatteringRate_pos
    (v m fermiEnergy disorderStrength hbar : ℝ)
    (hvelocity : v ≠ 0) (hhbar : 0 < hbar) (hdisorder : 0 < disorderStrength)
    (hm : 0 < m) (hmF : m < fermiEnergy) :
    0 < continuumBornUpperBandTransportScatteringRate
      v m fermiEnergy disorderStrength hbar := by
  rw [continuumBornUpperBandTransportScatteringRate_eq
    v m fermiEnergy disorderStrength hbar hvelocity (ne_of_gt hhbar) hm hmF]
  have hfermiPos : 0 < fermiEnergy := lt_trans hm hmF
  have hnum : 0 < fermiEnergy + 3 * m ^ 2 / fermiEnergy := by positivity
  have hden : 0 < 4 * hbar ^ 3 * v ^ 2 := by positivity
  exact mul_pos (div_pos hdisorder hden) hnum

/-- The transport rate relative to the single-particle rate is fixed entirely by the massive-Dirac
Fermi-circle angular structure. -/
theorem continuumBornUpperBandTransportRate_div_singleParticleRate
    (v m fermiEnergy disorderStrength hbar : ℝ)
    (hvelocity : v ≠ 0) (hhbar : 0 < hbar) (hdisorder : 0 < disorderStrength)
    (hm : 0 < m) (hmF : m < fermiEnergy) :
    continuumBornUpperBandTransportScatteringRate
        v m fermiEnergy disorderStrength hbar /
      continuumBornUpperBandSingleParticleScatteringRate
        v m fermiEnergy disorderStrength hbar =
      (fermiEnergy ^ 2 + 3 * m ^ 2) /
        (2 * (fermiEnergy ^ 2 + m ^ 2)) := by
  rw [continuumBornUpperBandTransportScatteringRate_eq
      v m fermiEnergy disorderStrength hbar hvelocity (ne_of_gt hhbar) hm hmF,
    continuumBornUpperBandSingleParticleScatteringRate_eq
      v m fermiEnergy disorderStrength hbar hvelocity (ne_of_gt hhbar) hm hmF]
  have hfermiNe : fermiEnergy ≠ 0 := ne_of_gt (lt_trans hm hmF)
  have hdisorderNe : disorderStrength ≠ 0 := ne_of_gt hdisorder
  field_simp [hvelocity, ne_of_gt hhbar, hfermiNe, hdisorderNe]
  ring

/-- Upper-band Born transport lifetime, defined as the reciprocal of the derived transport rate. -/
def continuumBornUpperBandTransportLifetime
    (v m fermiEnergy disorderStrength hbar : ℝ) : ℝ :=
  (continuumBornUpperBandTransportScatteringRate
    v m fermiEnergy disorderStrength hbar)⁻¹

/-- The microscopic Born transport lifetime is positive in the physical metallic regime. -/
theorem continuumBornUpperBandTransportLifetime_pos
    (v m fermiEnergy disorderStrength hbar : ℝ)
    (hvelocity : v ≠ 0) (hhbar : 0 < hbar) (hdisorder : 0 < disorderStrength)
    (hm : 0 < m) (hmF : m < fermiEnergy) :
    0 < continuumBornUpperBandTransportLifetime
      v m fermiEnergy disorderStrength hbar := by
  unfold continuumBornUpperBandTransportLifetime
  exact inv_pos.mpr
    (continuumBornUpperBandTransportScatteringRate_pos
      v m fermiEnergy disorderStrength hbar hvelocity hhbar hdisorder hm hmF)

/-- The transport lifetime is longer than the single-particle lifetime by the reciprocal angular
factor. -/
theorem continuumBornUpperBandTransportLifetime_eq_factor_mul_singleParticleLifetime
    (v m fermiEnergy disorderStrength hbar : ℝ)
    (hvelocity : v ≠ 0) (hhbar : 0 < hbar) (hdisorder : 0 < disorderStrength)
    (hm : 0 < m) (hmF : m < fermiEnergy) :
    continuumBornUpperBandTransportLifetime
        v m fermiEnergy disorderStrength hbar =
      (2 * (fermiEnergy ^ 2 + m ^ 2) /
          (fermiEnergy ^ 2 + 3 * m ^ 2)) *
        continuumBornUpperBandSingleParticleLifetime
          v m fermiEnergy disorderStrength hbar := by
  rw [continuumBornUpperBandTransportLifetime,
    continuumBornUpperBandSingleParticleLifetime]
  rw [continuumBornUpperBandTransportScatteringRate_eq
      v m fermiEnergy disorderStrength hbar hvelocity (ne_of_gt hhbar) hm hmF,
    continuumBornUpperBandSingleParticleScatteringRate_eq
      v m fermiEnergy disorderStrength hbar hvelocity (ne_of_gt hhbar) hm hmF]
  have hfermiPos : 0 < fermiEnergy := lt_trans hm hmF
  have hfermiNe : fermiEnergy ≠ 0 := ne_of_gt hfermiPos
  have hdisorderNe : disorderStrength ≠ 0 := ne_of_gt hdisorder
  have hsum1 : fermiEnergy ^ 2 + m ^ 2 ≠ 0 := by positivity
  have hsum3 : fermiEnergy ^ 2 + 3 * m ^ 2 ≠ 0 := by positivity
  field_simp [hvelocity, ne_of_gt hhbar, hfermiNe, hdisorderNe, hsum1, hsum3] <;> ring

/-- Package the microscopic Born transport lifetime as the generic positive current-relaxation datum
consumed by the longitudinal RTA benchmark.  This bridge does not identify the derivation with a
Kubo ladder resummation; it only records the positive scalar lifetime obtained from the Born angular
transport kernel above. -/
def continuumBornUpperBandPositiveTransportLifetime
    (v m fermiEnergy disorderStrength hbar : ℝ)
    (hvelocity : v ≠ 0) (hhbar : 0 < hbar) (hdisorder : 0 < disorderStrength)
    (hm : 0 < m) (hmF : m < fermiEnergy) : PositiveTransportLifetime where
  lifetime := continuumBornUpperBandTransportLifetime
    v m fermiEnergy disorderStrength hbar
  lifetime_pos := continuumBornUpperBandTransportLifetime_pos
    v m fermiEnergy disorderStrength hbar hvelocity hhbar hdisorder hm hmF

end

end AnomalousHall.MassiveDirac
